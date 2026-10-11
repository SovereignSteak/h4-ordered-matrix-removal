import H4Formal.PhysicalHostCore
import H4Formal.TerminalTypes

namespace H4Formal

set_option maxRecDepth 32768
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false

def markerPosition (h : Nat) (level : Fin h) (mode : Fin 6)
    (group : Fin 2) (offset : Fin (2 ^ h)) : PhysicalPosition h :=
  .inl (level, mode, group, offset)

def leafPosition (h : Nat) (p : Fin (2 ^ h)) : PhysicalPosition h :=
  .inr (.inr (.inl p))

def dummyPosition (h : Nat) (offset : Fin (2 ^ h)) : PhysicalPosition h :=
  .inr (.inr (.inr offset))

def terminalAnchorPosition (h : Nat) (hh : 0 < h) (parity group : Fin 2)
    (offset : Fin (2 ^ h)) : PhysicalPosition h :=
  markerPosition h ⟨h - 1, by omega⟩ ⟨4 + parity.val, by omega⟩ group offset

theorem terminal_parent_index_lt (h : Nat) (hh : 0 < h)
    (p : Fin (2 ^ h)) (offset : Fin 2) :
    2 * (p.val / 2) + offset.val < 2 ^ h := by
  have hm : 2 ^ h = 2 * 2 ^ (h - 1) := by
    calc
      2 ^ h = 2 ^ ((h - 1) + 1) := congrArg (fun n => 2 ^ n) (by omega)
      _ = 2 * 2 ^ (h - 1) := by rw [Nat.pow_succ, Nat.mul_comm]
  have hp := p.isLt
  have ho := offset.isLt
  omega

def terminalParentPosition (h : Nat) (hh : 0 < h) (p : Fin (2 ^ h))
    (offset : Fin 2) : PhysicalPosition h :=
  .inr (.inl (⟨h - 1, by omega⟩, 1,
    ⟨2 * (p.val / 2) + offset.val, terminal_parent_index_lt h hh p offset⟩))

def physicalCoordinate (h : Nat) : PhysicalPosition h → Fin (2 ^ h)
  | .inl (_, _, _, p) => p
  | .inr (.inl (_, _, p)) => p
  | .inr (.inr (.inl p)) => p
  | .inr (.inr (.inr p)) => p

@[simp] theorem terminalMode_code (h : Nat) (parity : Fin 2) :
    modeCode (terminalMode h parity.val) = 4 + parity.val := by
  fin_cases parity <;> rfl

@[simp] theorem terminalAnchorPosition_block (h : Nat) (hh : 0 < h)
    (parity group : Fin 2) (offset : Fin (2 ^ h)) :
    physicalBlock h (terminalAnchorPosition h hh parity group offset) =
      .anchor (terminalMode h parity.val) (group.val + 1) := by
  have hd : h - 1 + 1 = h := by omega
  fin_cases parity <;>
    simp [terminalAnchorPosition, markerPosition, physicalBlock, hd,
      modeFromCode, terminalMode]

@[simp] theorem leafPosition_block (h : Nat) (p : Fin (2 ^ h)) :
    physicalBlock h (leafPosition h p) = .variable h p.val .leaf := rfl

@[simp] theorem dummyPosition_block (h : Nat) (offset : Fin (2 ^ h)) :
    physicalBlock h (dummyPosition h offset) = .dummy := rfl

@[simp] theorem terminalParentPosition_block (h : Nat) (hh : 0 < h)
    (p : Fin (2 ^ h)) (offset : Fin 2) :
    physicalBlock h (terminalParentPosition h hh p offset) =
      .variable (h - 1) (p.val / 2) .minus := by
  have hd : h - (h - 1) = 1 := by omega
  have ho := offset.isLt
  simp only [terminalParentPosition, physicalBlock, hd, Nat.pow_one]
  congr 1
  omega

@[simp] theorem terminalParentPosition_offset (h : Nat) (hh : 0 < h)
    (p : Fin (2 ^ h)) (offset : Fin 2) :
    physicalOffset h (terminalParentPosition h hh p offset) = offset.val := by
  have hd : h - (h - 1) = 1 := by omega
  have ho := offset.isLt
  simp only [terminalParentPosition, physicalOffset, hd, Nat.pow_one]
  omega

theorem terminal_anchor_fiber (h : Nat) (hh : 0 < h) (parity group : Fin 2)
    (p : PhysicalPosition h)
    (he : physicalBlock h p = .anchor (terminalMode h parity.val) (group.val + 1)) :
    ∃ offset, p = terminalAnchorPosition h hh parity group offset := by
  rcases p with ⟨d, mode, g, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · have he' := Block.anchor.inj he
    have hd := congrArg Mode.depth he'.1
    have hm := congrArg modeCode he'.1
    change (modeFromCode mode.val (d.val + 1)).depth = h at hd
    rw [mode_from_code_depth] at hd
    change modeCode (modeFromCode mode.val (d.val + 1)) =
      modeCode (terminalMode h parity.val) at hm
    rw [mode_code_of_code mode.val (d.val + 1) (by omega), terminalMode_code] at hm
    have hdd : d = ⟨h - 1, by omega⟩ := by
      apply Fin.ext
      dsimp
      omega
    have hmm : mode = ⟨4 + parity.val, by omega⟩ := Fin.ext hm
    have hgg : g = group := Fin.ext (by omega)
    refine ⟨offset, ?_⟩
    simp only [terminalAnchorPosition, markerPosition, hdd, hmm, hgg]
  · simp [physicalBlock] at he
  · simp [physicalBlock] at he
  · simp [physicalBlock] at he

theorem terminal_leaf_fiber (h : Nat) (q : Fin (2 ^ h)) (p : PhysicalPosition h)
    (he : physicalBlock h p = .variable h q.val .leaf) : p = leafPosition h q := by
  rcases p with ⟨d, mode, g, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · simp [physicalBlock] at he
  · have hd := (Block.variable.inj he).1
    have hdlt := d.isLt
    omega
  · have hleaf : leaf = q := Fin.ext (Block.variable.inj he).2.1
    simp only [leafPosition, hleaf]
  · simp [physicalBlock] at he

theorem terminal_dummy_fiber (h : Nat) (p : PhysicalPosition h)
    (he : physicalBlock h p = .dummy) : ∃ offset, p = dummyPosition h offset := by
  rcases p with ⟨d, mode, g, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · simp [physicalBlock] at he
  · simp [physicalBlock] at he
  · simp [physicalBlock] at he
  · exact ⟨offset, rfl⟩

theorem terminal_parent_fiber (h : Nat) (hh : 0 < h) (q : Fin (2 ^ h))
    (p : PhysicalPosition h)
    (he : physicalBlock h p = .variable (h - 1) (q.val / 2) .minus) :
    ∃ offset, p = terminalParentPosition h hh q offset := by
  rcases p with ⟨d, mode, g, offset⟩ | (⟨d, sign, position⟩ | (leaf | offset))
  · simp [physicalBlock] at he
  · have he' := Block.variable.inj he
    have hd : d.val = h - 1 := he'.1
    have hdiff : h - d.val = 1 := by omega
    have hn : position.val / 2 = q.val / 2 := by
      simpa only [hdiff, Nat.pow_one] using he'.2.1
    have hs : sign = 1 := by
      fin_cases sign
      · simp [physicalBlock] at he
      · rfl
    let offset : Fin 2 := ⟨position.val % 2, Nat.mod_lt _ (by decide)⟩
    refine ⟨offset, ?_⟩
    have hdd : d = ⟨h - 1, by omega⟩ := Fin.ext hd
    have hp : position =
        ⟨2 * (q.val / 2) + offset.val, terminal_parent_index_lt h hh q offset⟩ := by
      apply Fin.ext
      dsimp [offset]
      omega
    simp only [terminalParentPosition, hdd, hs, hp]
  · have hd := (Block.variable.inj he).1
    omega
  · simp [physicalBlock] at he

end H4Formal
