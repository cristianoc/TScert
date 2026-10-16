open Semantic
open Environment
open Source
open Type_queries
open Object_spread
module type Inputs = sig
  include Analysis_capabilities.Queries
  include Analysis_capabilities.Execution_operations
  include Analysis_capabilities.Expression_publication
end
module Make (S : Inputs) = struct
open S
  let infer (expr:Analysis_state.expression_infer) initial plan =
    let rec input_names = function
      | Execution.Finish -> []
      | Execution.Input (name,_,_,next) -> name :: input_names next
      | Execution.DefaultValue (_,_,_,next) -> input_names next
      | Execution.Evaluate (_,_,next) | Execution.Bind (_,_,_,next)
      | Execution.ReadField (_,_,_,_,next) | Execution.ReadPosition (_,_,_,_,next)
      | Execution.ObjectRest (_,_,_,_,next) | Execution.ArrayRest (_,_,_,_,_,next) -> input_names next in
    let inputs=input_names plan in
    let env=List.filter (fun (name,_) -> not (List.mem name inputs)) initial in
    let get values saved = match List.assoc_opt saved.Execution.id values with
      | Some (t,_) -> t | None -> Json.fail "binding plan reads an unavailable saved value" in
    let put ?origin values saved t = (saved.Execution.id,(t,origin)) :: List.remove_assoc saved.Execution.id values in
    let publish source t instantiation =
      publish_expression source t instantiation in
    let rec defined_slice truth t = match t with
      | Union alternatives -> combine (List.map (defined_slice truth) alternatives)
      | Atoms atoms -> combine (List.map (fun atom ->
          match atom,expand_named declarations (Atoms [atom]) with
          | Named _,Some expanded when expanded <> Atoms [atom] -> defined_slice truth expanded
          | _ -> restrict Undef truth (Atoms [atom])) atoms)
      | t -> restrict Undef truth t in
    let rec run ?expected env values = function
      | Execution.Finish -> env
      | Execution.Input (name,_,value,next) ->
        run env (put values value (binding_type (lookup initial name))) next
      | Execution.Evaluate (value,plan,next) ->
        let source=Execution.source plan in
        let expression=match expression_hint source with
          | Some expression -> expression | None -> Json.fail "binding evaluation names missing expression" in
        let typing_env=match expression.node with
          | Lambda _ -> List.fold_left (fun scope name ->
              if List.mem_assoc name scope then scope else
                extend scope name (lookup initial name)) env inputs
          | _ -> env in
        let t=
          (try expr ?expected typing_env expression with
           | Json.Error message when inputs <> [] && String.starts_with ~prefix:"unbound name " message ->
             Proposal_diagnostics.unsupported ("parameter default may only read initialized earlier parameters and captures: " ^ message))
          in
        let origin = match expression.node with
          | Id name when (match List.assoc_opt name env with Some (Value _) -> true | _ -> false) -> Some name
          | _ -> None in
        run (run_execution env plan) (put ?origin values value t) next
      | Execution.DefaultValue (value,result,fallback,next) ->
        let t=get values value in
        let present=defined_slice false t and absent=defined_slice true t in
        if absent=Atoms [] then run env (put values result present) next
        else
          let source=Execution.source fallback in
          let expression=match expression_hint source with
            | Some expression -> expression | None -> Json.fail "binding default names missing expression" in
          let expected=if present=Atoms [] then None else Some present in
          let typing_env=match expression.node with
            | Lambda _ -> List.fold_left (fun scope name -> if List.mem_assoc name scope then scope
                else extend scope name (lookup initial name)) env inputs
            | _ -> env in
          let default=
            (try expr ?expected typing_env expression with
             | Json.Error message when inputs <> [] && String.starts_with ~prefix:"unbound name " message ->
               Proposal_diagnostics.unsupported ("parameter default may only read initialized earlier parameters and captures: " ^ message))
            in
          let after=run_execution env fallback in
          let after=if present=Atoms [] then after else join env env after in
          run after (put values result (union present default)) next
      | Execution.Bind (name,_,value,next) ->
        let t=get values value in
        let binding=match List.assoc_opt name initial with
          | Some (Storage (contract,_)) when List.mem name inputs -> holding contract t
          | Some (Local (contract,_)) when List.mem name inputs -> Local (contract,t)
          | _ -> Value t in
        run (extend env name binding) values next
      | Execution.ReadField (source,receiver,field,value,next) ->
        let observed = match List.assoc_opt receiver.Execution.id values with
          | Some (_,Some name) -> List.assoc_opt (field_key name field) env
          | _ -> None in
        let t=match observed with
          | Some binding -> binding_type binding
          | None -> S.field_type declarations [] (get values receiver) (Name field) in
        publish source t None;
        run env (put values value t) next
      | Execution.ReadPosition (_,array,index,value,next) ->
        let t=S.index_type declarations [] (get values array) (number_literal (string_of_int index)) in
        run (forget env) (put values value t) next
      | Execution.ObjectRest (source,receiver,drop,value,next) ->
        let drop=List.map (fun field -> Name field) drop in
        let alternatives=List.map (fun (a:alternative) ->
          {a with afields=List.filter (fun (f:Semantic.field) -> not (List.mem f.name drop)) a.afields})
          (source_alternatives declarations [] (get values receiver)) in
        let t=combine (List.map (fun a -> alternative_type
          (merge_alternative empty_alternative a)) alternatives) in
        publish source t None; run env (put values value t) next
      | Execution.ArrayRest (source,array,start,slice,value,next) ->
        let original=get values array in
        let t,instance=if slice then
          let element=slice_element declarations start original in
          array_type {required=[];optional_elements=[];rest=Some element;readonly=false;presence=Readable},
          Some ["T",ValueArgument element]
        else match declared_head declarations [] original with
          | Atoms [Shape {elements=Some shape;_}] when shape.optional_elements=[] && shape.rest=None ->
            array_type {required=List.filteri (fun index _ -> index>=start) shape.required;
              optional_elements=[];rest=None;readonly=false;presence=Dense},None
          | _ -> Proposal_diagnostics.unsupported "an array rest needs one tuple of required positions: the rest of an array of unknown length is a slice" in
        publish source t instance; run (forget env) (put values value t) next
    and array_type shape = Semantic.array shape in
    run env [] plan
  
end
