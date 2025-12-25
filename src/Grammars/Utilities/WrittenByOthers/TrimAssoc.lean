import Mathlib/Tactic

open Lean Elab Tactic

/--
`trim` is a lightweight replacement for the Lean 3 tactic that normalized chains of associative
operations such as list concatenation.  In Lean 4 the same effect can usually be achieved by `simp`
with the standard associativity/identity lemmas, so we expose it as a convenient macro to keep the
existing proofs readable.
-/
macro "trim" : tactic =>
  `(tactic|
    simp
      [List.append_assoc, List.nil_append, List.append_nil,
       List.map_append, List.map_cons, List.join, List.join_append, List.join_singleton,
       List.reverse_append, List.reverse_cons, List.repeat_succ_eq_singleton_append,
       List.repeat_succ_eq_append_singleton, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
       Nat.add_zero, Nat.zero_add, Nat.succ_eq_add_one, Nat.mul_assoc, Nat.mul_comm,
       Nat.mul_left_comm, Nat.mul_one, Nat.one_mul])
