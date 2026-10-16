open Semantic
open Source


(* A module function as its callers see it: an ordinary function at exactly its
   annotated parameters and result. A rest parameter contributes its tuple's
   positions or its array's element. Generic ones are not reachable yet. *)
(* A leading `this: T` parameter is the receiver, not a position. *)
let module_type (g:Source.fn) =
  let receiver,params = match g.params with
    | ("this",t) :: rest -> t,rest
    | params -> top,params in
  let tys = List.map snd params in
  match g.rest,List.rev tys with
  | true,_::before when g.rest_pack <> None ->
    Atoms [Shape {fields=[];indexes=[];elements=None;calls=[{quantified=g.quantified;receiver;
      params=List.rev before;variadic=None;rest_pack=Option.map (fun r -> PackParameter r) g.rest_pack;
      result=g.result;call_effect=Unrestricted}]}]
  | true,last::before ->
    (match Semantic.tuple_positions ~readonly:true last,Semantic.array_element ~readonly:true last with
     | Some positions,_ -> quantified_arrow ~receiver g.quantified (List.rev before @ positions) g.result
     | None,Some element -> variadic_arrow ~quantified:g.quantified ~receiver (List.rev before) element g.result
     | _ -> Proposal_diagnostics.unsupported "rest parameter contract of a module function")
  | _ -> quantified_arrow ~receiver g.quantified tys g.result

(* What a module function's code does with the actuals past its parameters.
   Code without a rest parameter discards them, so its slot also holds its
   signature extended by a rest of `unknown` elements (Lean's `moduleArrow`)
   and it meets a signature binding more parameters whose leading ones its own
   accept. A rest parameter collects them. A generic function is read at the
   instance its use names, a signature of its own parameters. *)
type arity = Discards | Collects | Instances
let arity (g:Source.fn) =
  if g.quantified <> [] then Instances else if g.rest then Collects else Discards

(* Why a function is refused where a signature binding more parameters is
   expected: a module function of the given arity, or a value known only by
   its type (`None`). *)
let longer_refusal = function
  | Some Discards -> None
  | Some Collects -> Some ("a function with a rest parameter where a signature binding more parameters is \
      expected: " ^ Proposal_diagnostics.rest_arity_reason)
  | Some Instances -> Some ("a generic module function where a signature binding more parameters is \
      expected: " ^ Proposal_diagnostics.module_arity_reason)
  | None -> Some ("a function value where a signature binding more parameters is expected: "
      ^ Proposal_diagnostics.value_arity_reason)

