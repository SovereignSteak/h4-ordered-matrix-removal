import H4Formal.Preservation

namespace H4Formal

/-!
# Compression witness restricted to the selected records

The depth-reduction argument has a finite support: the selected variable words
and the parent words needed by adjacent-level comparisons.  The witness below
quantifies only over that support.  This matches the finite construction and
does not impose global injectivity on every natural depth.
-/

structure SelectedWordCompressionWitness (support : List BinaryWord) where
  map : BinaryWord → BinaryWord
  depthMap : Nat → Nat
  length_map : ∀ u, u ∈ support → (map u).length = depthMap u.length
  depth_order : ∀ {u v}, u ∈ support → v ∈ support →
    (depthMap u.length = depthMap v.length ↔ u.length = v.length)
  prefix_iff : ∀ {u v}, u ∈ support → v ∈ support →
    ((map u) <+: (map v) ↔ u <+: v)
  length_lt_iff : ∀ {u v}, u ∈ support → v ∈ support →
    ((map u).length < (map v).length ↔ u.length < v.length)
  lex_iff : ∀ {u v}, u ∈ support → v ∈ support →
    (binaryLexLess (map u) (map v) ↔ binaryLexLess u v)
  first_divergence_defined_iff : ∀ {u v}, u ∈ support → v ∈ support →
    ((∃ d, firstDivergence (map u) (map v) = some d) ↔
      ∃ d, firstDivergence u v = some d)
  endpoint_iff : ∀ {u}, u ∈ support → endpointBit (map u) = endpointBit u
  parent_iff : ∀ {u}, u ∈ support →
    parentWord (map u) = map (parentWord u)

theorem SelectedWordCompressionWitness.properPrefix_iff
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support) :
    properPrefix (w.map u) (w.map v) ↔ properPrefix u v := by
  simp [properPrefix, w.prefix_iff hu hv, w.length_lt_iff hu hv]

theorem SelectedWordCompressionWitness.firstDivergence_defined_preserved
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support) :
    (∃ d, firstDivergence (w.map u) (w.map v) = some d) ↔
      ∃ d, firstDivergence u v = some d :=
  w.first_divergence_defined_iff hu hv

theorem SelectedWordCompressionWitness.lex_preserved
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u v : BinaryWord} (hu : u ∈ support) (hv : v ∈ support) :
    binaryLexLess (w.map u) (w.map v) ↔ binaryLexLess u v :=
  w.lex_iff hu hv

theorem SelectedWordCompressionWitness.endpoint_preserved
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u : BinaryWord} (hu : u ∈ support) :
    endpointBit (w.map u) = endpointBit u :=
  w.endpoint_iff hu

theorem SelectedWordCompressionWitness.parent_preserved
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    {u : BinaryWord} (hu : u ∈ support) :
    parentWord (w.map u) = w.map (parentWord u) :=
  w.parent_iff hu

structure SignedWord where
  word : BinaryWord
  sign : Sign
  deriving DecidableEq, Repr

def sameDepthSignBefore (axis : Axis) (a b : Sign) : Prop :=
  if axis = .row then a = .minus ∧ b = .plus
  else a = .plus ∧ b = .minus

def ancestorSignBefore (axis : Axis) (a : Sign) : Prop :=
  if axis = .row then a = .minus else a = .plus

def descendantSignBefore (axis : Axis) (a : Sign) : Prop :=
  if axis = .row then a = .plus else a = .minus

def variableBefore (axis : Axis) (a b : SignedWord) : Prop :=
  if a.word <+: b.word then
    if a.word.length = b.word.length then
      sameDepthSignBefore axis a.sign b.sign
    else ancestorSignBefore axis a.sign
  else if b.word <+: a.word then
    descendantSignBefore axis b.sign
  else binaryLexLess a.word b.word

def mapSigned (w : SelectedWordCompressionWitness support) (x : SignedWord) : SignedWord :=
  { word := w.map x.word, sign := x.sign }

theorem variableBefore_preserved
    {support : List BinaryWord} (w : SelectedWordCompressionWitness support)
    (axis : Axis) (a b : SignedWord)
    (ha : a.word ∈ support) (hb : b.word ∈ support) :
    variableBefore axis (mapSigned w a) (mapSigned w b) ↔
      variableBefore axis a b := by
  by_cases hab : a.word <+: b.word
  · have hmap : w.map a.word <+: w.map b.word :=
      w.prefix_iff ha hb |>.2 hab
    by_cases hlen : a.word.length = b.word.length
    · have hmaplen : (w.map a.word).length = (w.map b.word).length := by
        rw [w.length_map a.word ha, w.length_map b.word hb]
        exact (w.depth_order ha hb).2 hlen
      simp [mapSigned, variableBefore, hab, hmap, hlen, hmaplen]
    · have hmaplen : (w.map a.word).length ≠ (w.map b.word).length := by
        intro heq
        have hdepth : w.depthMap a.word.length = w.depthMap b.word.length := by
          rw [← w.length_map a.word ha, ← w.length_map b.word hb]
          exact heq
        apply hlen
        exact (w.depth_order ha hb).1 hdepth
      simp [mapSigned, variableBefore, hab, hmap, hlen, hmaplen]
  · have hmap : ¬ w.map a.word <+: w.map b.word := by
      intro h
      apply hab
      exact (w.prefix_iff ha hb).1 h
    by_cases hba : b.word <+: a.word
    · have hmap' : w.map b.word <+: w.map a.word :=
        w.prefix_iff hb ha |>.2 hba
      simp [mapSigned, variableBefore, hab, hmap, hba, hmap']
    · have hmap' : ¬ w.map b.word <+: w.map a.word := by
        intro h
        apply hba
        exact (w.prefix_iff hb ha).1 h
      simp [mapSigned, variableBefore, hab, hmap, hba, hmap', w.lex_iff ha hb]

end H4Formal
