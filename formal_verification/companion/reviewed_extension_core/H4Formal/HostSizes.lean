import H4Formal.ConcreteCompression

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0

def branchFactor (h : Nat) : Nat := 2 ^ h

def hostSideLength (h : Nat) : Nat := (14 * h + 2) * branchFactor h

def canonicalRepairCellCount (h : Nat) : Nat := branchFactor h ^ 2

theorem canonicalRepairCellCount_eq_power (h : Nat) :
    canonicalRepairCellCount h = 2 ^ (2 * h) := by
  unfold canonicalRepairCellCount branchFactor
  simpa [Nat.mul_comm] using (Nat.pow_mul 2 h 2).symm

end H4Formal
