
module Nat :
 sig
  val eqb : int -> int -> bool

  val leb : int -> int -> bool
 end

type agent = int
  (* singleton inductive, whose constructor was mkAgent *)

val agent_eqb : agent -> agent -> bool

type obligation =
  int
  (* singleton inductive, whose constructor was mkObligation *)

val obligation_eqb : obligation -> obligation -> bool

type severity = int

type deonticSystem = { agents : agent list;
                       obligated : (agent -> obligation -> bool);
                       violated : (agent -> obligation -> bool);
                       may_enforce : (agent -> agent -> bool);
                       severity_cap : (obligation -> severity) }

type punitiveResponse = { enforcer : agent; target : agent;
                          cause : obligation; severity0 : severity }

val in_agentb : agent -> agent list -> bool

val authorizedb : deonticSystem -> punitiveResponse -> bool

val boundedb : deonticSystem -> punitiveResponse -> bool

val lawfulb : deonticSystem -> punitiveResponse -> bool
