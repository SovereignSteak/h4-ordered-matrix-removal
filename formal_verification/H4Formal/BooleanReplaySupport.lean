import H4Formal.ArithmeticReplaySupport

syntax "h4_bool_congr" : tactic

macro_rules
  | `(tactic| h4_bool_congr) => `(tactic|
      first
      | exact Iff.rfl
      | (apply and_congr <;> h4_bool_congr)
      | (apply or_congr <;> h4_bool_congr)
      | (apply not_congr; h4_bool_congr)
      | (apply imp_congr <;> h4_bool_congr)
      | (apply iff_congr <;> h4_bool_congr)
      | (apply Iff.of_eq; ac_rfl))
