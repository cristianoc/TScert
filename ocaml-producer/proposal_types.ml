(* Candidate claims shared by inference and serialization. *)
open Semantic
open Environment
open Source

type entry = { point: string; start: Json.t; bindings: (string * binding) list }
(* A call site's proposed substitution travels with its claim. It is proposal
   output for Lean to re-check, never an acceptance fact. *)
type expression = { point: string; pos: Json.t; type_: ty; instantiation: (string * type_argument) list option }
(* One closure advertising several signatures has one body and a separate
   obligation at each: the interior claims are collected once per signature,
   keyed by the closure's span and ordered with the signatures. *)
type contract = { pos: Json.t; name: string; type_: ty }
type overlay = { row_contracts: contract list; row_entries: entry list; row_expressions: expression list }
type function_claim = { contracts: contract list; source: fn; entries: entry list; expressions: expression list;
                        arrows: (Json.t * overlay list) list }
type t = { program: program; functions: function_claim list; init: function_claim option }
