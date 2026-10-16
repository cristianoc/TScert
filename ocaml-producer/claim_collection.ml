open Semantic
open Environment
open Source
open Refinement
module type Inputs = sig
  val declarations : Source.declaration list
  val is_local : string -> bool
  val module_type : string -> Semantic.ty option
  val publish_instance : Json.t -> Semantic.ty -> unit
  val publish_entry : Json.t -> (string * Environment.binding) list -> unit
  val speculate : (unit -> 'a) -> 'a option
end

module Make (S : Inputs) = struct
open S
  let instance_of ?declared (callee:expr) substitution =
    match callee.node with
    (* A generic method read from its object is claimed at the instance the
       call names: Lean puts the method's scheme below it. *)
    | Read _ | Index _ ->
      (match declared with
       | Some (Atoms [Shape ({calls=[signature];_} as shape)]) ->
         let instance = Inference.substitute substitution
           (Atoms [Shape {shape with calls=[{signature with quantified=[]}]}]) in
         publish_instance callee.pos instance
       | _ -> ())
    | Id n when not (is_local n) ->
      (match module_type n with
       | Some (Atoms [Shape ({calls=[signature];_} as shape)]) ->
         let instance = Inference.substitute substitution
           (Atoms [Shape {shape with calls=[{signature with quantified=[]}]}]) in
         publish_instance callee.pos instance
       | Some (Atoms [Ctors ([signature],statics)]) ->
         let instance = Inference.substitute substitution
           (Atoms [Ctors ([{signature with quantified=[]}],statics)]) in
         publish_instance callee.pos instance
       | _ -> ())
    | _ -> ()

  let method_read (callee:expr) = match callee.node with
    | Read _ | Index _ -> true | _ -> false

  let quietly = S.speculate

  let entry env span = match Json.list span with
    | start::_ ->
      (* A read-result observation is claimed where every record arm names the key. *)
      let bindings = List.filter (fun (n,_) -> not (is_field n) ||
        (match List.assoc_opt (owner n) env with
         | Some (Value t) -> record_field ~allow_optional:true declarations t (field_of n)
         | _ -> false)) env in
      publish_entry start bindings
    | [] -> Json.fail "empty source span"

end
