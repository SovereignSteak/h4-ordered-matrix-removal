import H4Formal.Host

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

def multiplicity (h : Nat) : Block → Nat
  | .anchor _ _ => 2 ^ h
  | .dummy => 2 ^ h
  | .variable depth _ sign =>
      match sign with
      | .leaf => 1
      | .plus => 2 ^ (h - depth)
      | .minus => 2 ^ (h - depth)

end H4Formal
