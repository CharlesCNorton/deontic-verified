
module Nat =
 struct
  (** val eqb : int -> int -> bool **)

  let rec eqb n m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> true)
        (fun _ -> false)
        m)
      (fun n' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> false)
        (fun m' -> eqb n' m')
        m)
      n

  (** val leb : int -> int -> bool **)

  let rec leb n m =
    (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
      (fun _ -> true)
      (fun n' ->
      (fun fO fS n -> if n = 0 then fO () else fS (n - 1))
        (fun _ -> false)
        (fun m' -> leb n' m')
        m)
      n
 end

type agent = int
  (* singleton inductive, whose constructor was mkAgent *)

(** val agent_eqb : agent -> agent -> bool **)

let agent_eqb =
  Nat.eqb

type obligation =
  int
  (* singleton inductive, whose constructor was mkObligation *)

(** val obligation_eqb : obligation -> obligation -> bool **)

let obligation_eqb =
  Nat.eqb

type severity = int

type deonticSystem = { agents : agent list;
                       obligated : (agent -> obligation -> bool);
                       violated : (agent -> obligation -> bool);
                       may_enforce : (agent -> agent -> bool);
                       severity_cap : (obligation -> severity) }

type punitiveResponse = { enforcer : agent; target : agent;
                          cause : obligation; severity0 : severity }

(** val in_agentb : agent -> agent list -> bool **)

let rec in_agentb a = function
| [] -> false
| x::rest -> if agent_eqb a x then true else in_agentb a rest

(** val authorizedb : deonticSystem -> punitiveResponse -> bool **)

let authorizedb ds pr =
  if if if if in_agentb pr.enforcer ds.agents
           then in_agentb pr.target ds.agents
           else false
        then ds.may_enforce pr.enforcer pr.target
        else false
     then ds.violated pr.target pr.cause
     else false
  then ds.obligated pr.target pr.cause
  else false

(** val boundedb : deonticSystem -> punitiveResponse -> bool **)

let boundedb ds pr =
  Nat.leb pr.severity0 (ds.severity_cap pr.cause)

(** val lawfulb : deonticSystem -> punitiveResponse -> bool **)

let lawfulb ds pr =
  if authorizedb ds pr then boundedb ds pr else false
