import Submission.Obl.k4_scalar_tangent_isotropic_improvement.GraphBad

set_option linter.unusedVariables false

/-!
# The physical velocity graph in one world

`graph_world` assembles the velocity graph of the paper (`a05:velocity-graph`) for one world at
one sample: light fine cubes are deleted (`light_deletion`), heavy cubes without a capturing plane
are bad and carry little mass (`frozen_bad_mass_le`), heavy cubes with a capturing plane keep
their captured incidences, on which one bounded row `G q` fits `x' = G₀ + G₁ V`
(`good_cell_graph`). Outputs: the retained set `E ⊆ E₀` with its mass bound, the pointwise graph
residual, and the mass floor `(1 - c) λ` of every fine cube meeting `E` (used for fine-state
palette domination).
-/

namespace Submission.Obl.k4_scalar_tangent_isotropic_improvement

open MeasureTheory Set Submission.Lib.K4ContinuousKakeya
open scoped ENNReal NNReal

noncomputable section

local notation "E3" => EuclideanSpace ℝ (Fin 3)

lemma physIn_eq_of_mem {E : Set Inc} {p : Inc} (hp : p ∈ E) : physIn E p = physOf p := by
  classical
  simp [physIn, hp]

lemma physIn_preimage_cellSet {E : Set Inc} {w : ℝ} (hw : 0 < w) {q : Fin 3 → ℤ} (hq : 0 ≤ q 0) :
    physIn E ⁻¹' cellSet w q = E ∩ physOf ⁻¹' cellSet w q := by
  ext p
  constructor
  · intro h; exact physIn_mem_cellSet hw hq h
  · rintro ⟨hpE, hp⟩; show physIn E p ∈ cellSet w q; rwa [physIn_eq_of_mem hpE]

lemma measurableSet_physOf_preimage (w : ℝ) (q : Fin 3 → ℤ) :
    MeasurableSet (physOf ⁻¹' cellSet w q) :=
  continuous_physOf.measurable (measurableSet_cellSet w q)

/-- **The physical velocity graph in one world.** Fine cubes of side `b`, coarse cubes of side
`M₀ b`, light cubes (`ρ|E₀`-mass below `λ`) deleted, bad cubes (no capturing plane) controlled by
`frozen_bad_mass_le`, good cubes replaced by their captured incidences on which one bounded row
`G q` fits `x' = G₀ + G₁ V`. The output `E ⊆ E₀` loses at most the light mass, the bad mass and a
fraction `c` of the good mass; every cube meeting `E` keeps mass `≥ (1 - c) λ`. -/
theorem graph_world {C : ℝ} (hC0 : 0 ≤ C) (hC : FiniteMK 3 C)
    (θ : Measure (ℕ × (Fin 5 → ℝ))) [IsFiniteMeasure θ] (ρ : Measure Inc) [IsFiniteMeasure ρ]
    {E₀ : Set Inc} (hE₀ : MeasurableSet E₀) {H : ℝ} (hH : 1 ≤ H)
    (hle : ρ.restrict E₀ ≤ H.toNNReal • (θ.prod volume).restrict E₀)
    (hge : (θ.prod volume).restrict E₀ ≤ H.toNNReal • ρ.restrict E₀)
    (hE₀H : ∀ p ∈ E₀, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H)
    {b : ℝ} (hb : 0 < b) (hb1 : b ≤ 1) {M₀ : ℕ} (hM₀ : 1 ≤ M₀) (hw₀1 : (M₀ : ℝ) * b ≤ 1)
    (Occ : Finset (Fin 3 → ℤ))
    (hOcc : ∀ q, ρ.restrict E₀ (physOf ⁻¹' cellSet b q) ≠ 0 → q ∈ Occ)
    {capQ : ℝ} (hcapQ : ∀ Q, ρ (physOf ⁻¹' cellSet ((M₀ : ℝ) * b) Q) ≤ ENNReal.ofReal capQ)
    {δ Wmax lam ε c η : ℝ} (hδ : 0 < δ) (hlam : 0 < lam)
    (hwin : ∀ q (v₀ : ℝ), ρ {p | p ∈ physOf ⁻¹' cellSet b q ∧ |p.1.2 1 - v₀| < δ} ≤
      ENNReal.ofReal Wmax)
    (hWmax : Wmax ≤ (1 - c) * lam)
    (τ₀ : ℝ≥0) (hτ₀ : 0 < τ₀) (hε : 0 < ε) (hc : 0 ≤ c) (hc1 : c < 1)
    (hη : 0 < η) (hη4 : η ≤ 1 / 4) (hp₀ : 2 * ((3 : ℕ) : ℝ) * η ≤ c ^ 2)
    (hsmall : ε * (1 + 4 * H) * (1 + 2 * (3 * H + 1) / δ) ≤ 1 / 2)
    (hβ' : 0 < ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H * ((M₀ : ℝ) * b)))
    (hcontr : ((⌊capQ / lam⌋₊ : ℕ) : ℝ) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
        (2 ^ (3 : ℕ) * C * (2 * b + H * ((M₀ : ℝ) * b) ^ 2) ^ (3 : ℕ) / b ^ 3 *
          ((H.toNNReal * b.toNNReal : ℝ≥0) : ℝ) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1)) /
          ((ε ^ 2 - (Nat.factorial 3) * (3 : ℕ) * (4 * H * ((M₀ : ℝ) * b))) *
            (c ^ 2 - (3 : ℕ) * η)) ^ ((1 : ℝ) / (((3 : ℕ) : ℝ) - 1)) *
          ((H.toNNReal : ℝ) / τ₀) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1))) ≤
        (1 / 2) ^ (((3 : ℕ) : ℝ) / (((3 : ℕ) : ℝ) - 1))) :
    ∃ (E : Set Inc) (G : (Fin 3 → ℤ) → ℝ × ℝ), MeasurableSet E ∧ E ⊆ E₀ ∧
      (ρ.restrict E₀ Set.univ).toReal ≤ (ρ.restrict E Set.univ).toReal / (1 - c) +
        Occ.card * lam + 3 / η * (H.toNNReal * τ₀ *
          (((⌊1 / ((M₀ : ℝ) * b)⌋₊ + 1) * (2 * (⌈H⌉₊ + 1) + 1) * (2 * (⌈3 * H⌉₊ + 1) + 1) : ℕ) *
            (θ Set.univ).toReal)) ∧
      (∀ p ∈ E, |(G (cellIdx b (physOf p))).1| ≤ 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) ∧
        |(G (cellIdx b (physOf p))).2| ≤ 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) ∧
        |(p.1.2 3 + 2 * p.1.2 4 * p.2) - (G (cellIdx b (physOf p))).1 -
            (G (cellIdx b (physOf p))).2 * p.1.2 1| ≤
          ε * (1 + 4 * H) * (2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)))) ∧
      (∀ q, ρ.restrict E (physOf ⁻¹' cellSet b q) ≠ 0 →
        ENNReal.ofReal ((1 - c) * lam) ≤ ρ.restrict E (physOf ⁻¹' cellSet b q)) := by
  classical
  set w₀ : ℝ := (M₀ : ℝ) * b with hw₀
  have hw₀pos : 0 < w₀ := mul_pos (by exact_mod_cast hM₀) hb
  have hH0 : 0 ≤ H := by linarith
  set E₁ : Set Inc := E₀ ∩ {p | cellIdx b (physOf p) ∈ heavyCells ρ E₀ b lam} with hE₁
  have hE₁m : MeasurableSet E₁ := hE₀.inter (measurableSet_preimage_cellIdx b _)
  have hE₁sub : E₁ ⊆ E₀ := Set.inter_subset_left
  have hE₁H : ∀ p ∈ E₁, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ e, |p.1.2 e| ≤ H :=
    fun p hp => hE₀H p hp.1
  set inc : Measure Inc := ρ.restrict E₁ with hinc
  have hle1 : inc ≤ H.toNNReal • (θ.prod volume).restrict E₁ := by
    rw [hinc, ← Measure.restrict_restrict_of_subset hE₁sub,
      ← Measure.restrict_restrict_of_subset (μ := θ.prod volume) hE₁sub, ← Measure.restrict_smul]
    exact Measure.restrict_mono le_rfl hle
  have hge1 : (θ.prod volume).restrict E₁ ≤ H.toNNReal • inc := by
    have e1 : (θ.prod volume).restrict E₁ = ((θ.prod volume).restrict E₀).restrict E₁ :=
      (Measure.restrict_restrict_of_subset hE₁sub).symm
    have e2 : inc = (ρ.restrict E₀).restrict E₁ := (Measure.restrict_restrict_of_subset hE₁sub).symm
    rw [e1, e2, ← Measure.restrict_smul]
    exact Measure.restrict_mono le_rfl hge
  have hcellm : ∀ q, MeasurableSet (physOf ⁻¹' cellSet b q) := measurableSet_physOf_preimage b
  -- heavy occupied cells
  set HOcc : Finset (Fin 3 → ℤ) := Occ.filter (fun q => q ∈ heavyCells ρ E₀ b lam) with hHOcc
  have hHmass : ∀ q ∈ HOcc, ENNReal.ofReal lam ≤ ρ.restrict E₀ (physOf ⁻¹' cellSet b q) := by
    intro q hq
    have := (Finset.mem_filter.mp hq).2
    simpa [heavyCells, cellSet] using this
  have hHq0 : ∀ q ∈ HOcc, 0 ≤ q 0 := by
    intro q hq
    have hpos : ρ.restrict E₀ (physOf ⁻¹' cellSet b q) ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hlam) (hHmass q hq)).ne'
    rw [Measure.restrict_apply (hcellm q)] at hpos
    obtain ⟨p, hpcell, hpE⟩ := nonempty_of_measure_ne_zero hpos
    have h1 := (time_mem_of_mem_cellSet hb hpcell).2
    have h2 := (hE₀H p hpE).1.1
    by_contra hneg
    have hneg' : q 0 + 1 ≤ 0 := by omega
    have : (q 0 : ℝ) + 1 ≤ 0 := by exact_mod_cast hneg'
    nlinarith
  -- the incidence law of a heavy cell is its whole ρ|E₀ law
  have hX : ∀ q ∈ HOcc, physIn E₁ ⁻¹' cellSet b q = E₁ ∩ physOf ⁻¹' cellSet b q :=
    fun q hq => physIn_preimage_cellSet hb (hHq0 q hq)
  have hincX : ∀ q ∈ HOcc, inc (physIn E₁ ⁻¹' cellSet b q) =
      ρ.restrict E₀ (physOf ⁻¹' cellSet b q) := by
    intro q hq
    rw [hX q hq, hinc, Measure.restrict_apply (hE₁m.inter (hcellm q)),
      Measure.restrict_apply (hcellm q)]
    congr 1
    ext p
    simp only [Set.mem_inter_iff, Set.mem_preimage, hE₁, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨⟨hpE, _⟩, hpc⟩, _⟩; exact ⟨hpc, hpE⟩
    · rintro ⟨hpc, hpE⟩
      have hh : cellIdx b (physOf p) ∈ heavyCells ρ E₀ b lam := by
        have : cellIdx b (physOf p) = q := hpc
        rw [this]; exact (Finset.mem_filter.mp hq).2
      exact ⟨⟨⟨hpE, hh⟩, hpc⟩, ⟨hpE, hh⟩⟩
  have hincXlam : ∀ q ∈ HOcc, ENNReal.ofReal lam ≤ inc (physIn E₁ ⁻¹' cellSet b q) :=
    fun q hq => (hincX q hq).symm ▸ hHmass q hq
  -- classification of heavy cells
  let bad : (Fin 3 → ℤ) → Prop := fun q => ∀ ν : E3, ‖ν‖ = 1 →
      inc {ω | ω ∈ physIn E₁ ⁻¹' cellSet b q ∧ |inner ℝ ν (unitOf ω)| < ε} ≤
        ENNReal.ofReal (1 - c) * inc (physIn E₁ ⁻¹' cellSet b q)
  set BadF : Finset (Fin 3 → ℤ) := HOcc.filter bad with hBadF
  set GoodF : Finset (Fin 3 → ℤ) := HOcc.filter (fun q => ¬ bad q) with hGoodF
  have hBadsub : BadF ⊆ HOcc := Finset.filter_subset _ _
  have hGoodsub : GoodF ⊆ HOcc := Finset.filter_subset _ _
  have hXm : ∀ q, MeasurableSet (physIn E₁ ⁻¹' cellSet b q) :=
    fun q => (measurable_physIn hE₁m) (measurableSet_cellSet b q)
  have hoccB : ∀ q ∈ BadF, ∃ p ∈ E₁, physOf p ∈ cellSet b q := by
    intro q hq
    have hqH := hBadsub hq
    have hpos : inc (physIn E₁ ⁻¹' cellSet b q) ≠ 0 :=
      (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hlam) (hincXlam q hqH)).ne'
    obtain ⟨p, hp⟩ := nonempty_of_measure_ne_zero hpos
    exact ⟨p, (physIn_mem_cellSet hb (hHq0 q hqH) hp).1, (physIn_mem_cellSet hb (hHq0 q hqH) hp).2⟩
  -- the support count per coarse cube
  have hS₀ : ∀ Q, (BadF.filter (fun q => cubeOf M₀ q = Q)).card ≤ ⌊capQ / lam⌋₊ := by
    intro Q
    set F := BadF.filter (fun q => cubeOf M₀ q = Q) with hF
    have hdisjF : (F : Set (Fin 3 → ℤ)).PairwiseDisjoint (fun q => physIn E₁ ⁻¹' cellSet b q) := by
      intro q _ q' _ hqq'
      rw [Function.onFun, Set.disjoint_iff]
      intro x ⟨hx, hx'⟩
      exact hqq' (hx.symm.trans hx')
    have hsum : ∑ q ∈ F, inc (physIn E₁ ⁻¹' cellSet b q) ≤ ENNReal.ofReal capQ := by
      calc ∑ q ∈ F, inc (physIn E₁ ⁻¹' cellSet b q)
          = inc (⋃ q ∈ F, physIn E₁ ⁻¹' cellSet b q) :=
            (measure_biUnion_finset hdisjF (fun q _ => hXm q)).symm
        _ ≤ ρ (⋃ q ∈ F, physIn E₁ ⁻¹' cellSet b q) := Measure.restrict_le_self _
        _ ≤ ρ (physOf ⁻¹' cellSet ((M₀ : ℝ) * b) Q) := by
            apply measure_mono
            intro p hp
            simp only [Set.mem_iUnion] at hp
            obtain ⟨q, hq, hpq⟩ := hp
            have hqB := (Finset.mem_filter.mp hq)
            have hq0' := hHq0 q (hBadsub hqB.1)
            have hphys := (physIn_mem_cellSet hb hq0' hpq).2
            show cellIdx ((M₀ : ℝ) * b) (physOf p) = Q
            rw [cellIdx_coarse hb M₀]
            have : cellIdx b (physOf p) = q := hphys
            rw [this, hqB.2]
        _ ≤ ENNReal.ofReal capQ := hcapQ Q
    have hlow : F.card • ENNReal.ofReal lam ≤ ∑ q ∈ F, inc (physIn E₁ ⁻¹' cellSet b q) :=
      Finset.card_nsmul_le_sum _ _ _ (fun q hq => hincXlam q (hBadsub (Finset.mem_filter.mp hq).1))
    have hle' : ENNReal.ofReal (F.card * lam) ≤ ENNReal.ofReal capQ := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast, ← nsmul_eq_mul]
      exact hlow.trans hsum
    by_cases hFe : F.card = 0
    · rw [hFe]; exact Nat.zero_le _
    have hpos : 0 < ENNReal.ofReal (F.card * lam) :=
      ENNReal.ofReal_pos.mpr (mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hFe) hlam)
    have hcapQ0 : 0 ≤ capQ := by
      by_contra hneg
      have : ENNReal.ofReal capQ = 0 := ENNReal.ofReal_of_nonpos (le_of_lt (not_le.mp hneg))
      rw [this] at hle'
      exact absurd hle' (not_le.mpr hpos)
    apply Nat.le_floor
    rw [le_div_iff₀ hlam]
    exact (ENNReal.ofReal_le_ofReal_iff hcapQ0).mp hle'
  -- the bad cells carry little mass
  have hbadmass := frozen_bad_mass_le hC0 hC θ inc hE₁m hH hle1 hge1 hE₁H hb hb1 hM₀ hw₀1 BadF
    hoccB τ₀ hτ₀ hε hc hc1.le hη hη4 hp₀ (fun q hq => (Finset.mem_filter.mp hq).2)
    ⌊capQ / lam⌋₊ hS₀ hβ' hcontr
  -- good cells: a capturing plane and a bounded row
  have hgood : ∀ q ∈ GoodF, ∃ ν : E3, ‖ν‖ = 1 ∧ ENNReal.ofReal (1 - c) * inc (physIn E₁ ⁻¹' cellSet b q) <
      inc {ω | ω ∈ physIn E₁ ⁻¹' cellSet b q ∧ |inner ℝ ν (unitOf ω)| < ε} := by
    intro q hq
    have hnb := (Finset.mem_filter.mp hq).2
    simp only [bad, not_forall, not_le] at hnb
    obtain ⟨ν, hν, hlt⟩ := hnb
    exact ⟨ν, hν, hlt⟩
  choose ν hν using hgood
  have hXH : ∀ q ∈ GoodF, ∀ p ∈ physIn E₁ ⁻¹' cellSet b q, p.2 ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ e, |p.1.2 e| ≤ H := by
    intro q hq p hp
    exact hE₁H p (physIn_mem_cellSet hb (hHq0 q (hGoodsub hq)) hp).1
  have hgraph : ∀ q (hq : q ∈ GoodF), ∃ G₀ G₁ : ℝ,
      |G₀| ≤ 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) ∧
      |G₁| ≤ 2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1)) ∧
      ∀ p, p ∈ physIn E₁ ⁻¹' cellSet b q → |inner ℝ (ν q hq) (unitOf p)| < ε →
        |(p.1.2 3 + 2 * p.1.2 4 * p.2) - G₀ - G₁ * p.1.2 1| ≤
          ε * (1 + 4 * H) * (2 * ((3 * H + 1) * (2 * (3 * H) / δ + 1))) := by
    intro q hq
    apply good_cell_graph inc (hXm q) hH0 hδ (hXH q hq) (ν q hq) (hν q hq).1 (hν q hq).2 _ hsmall
    intro v₀
    calc inc {p | p ∈ physIn E₁ ⁻¹' cellSet b q ∧ |p.1.2 1 - v₀| < δ}
        ≤ ρ {p | p ∈ physOf ⁻¹' cellSet b q ∧ |p.1.2 1 - v₀| < δ} := by
          refine (Measure.restrict_le_self _).trans (measure_mono ?_)
          intro p ⟨hp, hpv⟩
          exact ⟨(physIn_mem_cellSet hb (hHq0 q (hGoodsub hq)) hp).2, hpv⟩
      _ ≤ ENNReal.ofReal Wmax := hwin q v₀
      _ ≤ ENNReal.ofReal ((1 - c) * lam) := ENNReal.ofReal_le_ofReal hWmax
      _ = ENNReal.ofReal (1 - c) * ENNReal.ofReal lam := ENNReal.ofReal_mul (by linarith)
      _ ≤ ENNReal.ofReal (1 - c) * inc (physIn E₁ ⁻¹' cellSet b q) := by
          gcongr; exact hincXlam q (hGoodsub hq)
  choose G₀ G₁ hG using hgraph
  -- the retained incidences and the rows
  set Cap : (q : Fin 3 → ℤ) → q ∈ GoodF → Set Inc := fun q hq =>
    {p | p ∈ physIn E₁ ⁻¹' cellSet b q ∧ |inner ℝ (ν q hq) (unitOf p)| < ε} with hCap
  have hCapm : ∀ q hq, MeasurableSet (Cap q hq) := by
    intro q hq
    have hm : Measurable fun p : Inc => |inner ℝ (ν q hq) (unitOf p)| :=
      ((continuous_const.inner continuous_unitOf).abs).measurable
    exact (hXm q).inter (measurableSet_lt hm measurable_const)
  set E : Set Inc := ⋃ q, ⋃ (hq : q ∈ GoodF), Cap q hq with hEdef
  set G : (Fin 3 → ℤ) → ℝ × ℝ := fun q => if hq : q ∈ GoodF then (G₀ q hq, G₁ q hq) else (0, 0)
    with hGdef
  have hEm : MeasurableSet E := MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq => hCapm q hq
  have hCapsub : ∀ q hq, Cap q hq ⊆ E₁ ∩ physOf ⁻¹' cellSet b q := fun q hq p hp =>
    physIn_mem_cellSet hb (hHq0 q (hGoodsub hq)) hp.1
  have hEsub1 : E ⊆ E₁ := by
    intro p hp
    simp only [hEdef, Set.mem_iUnion] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    exact (hCapsub q hq hpq).1
  refine ⟨E, G, hEm, hEsub1.trans hE₁sub, ?_, ?_, ?_⟩
  · -- the mass bound
    set Cap' : (Fin 3 → ℤ) → Set Inc := fun q => if h : q ∈ GoodF then Cap q h else ∅ with hCap'
    have hCap'm : ∀ q, MeasurableSet (Cap' q) := fun q => by
      by_cases h : q ∈ GoodF
      · simp only [hCap', dif_pos h]; exact hCapm q h
      · simp only [hCap', dif_neg h]; exact MeasurableSet.empty
    have hCap'sub : ∀ q, Cap' q ⊆ physIn E₁ ⁻¹' cellSet b q := fun q p hp => by
      by_cases h : q ∈ GoodF
      · simp only [hCap', dif_pos h] at hp; exact hp.1
      · simp only [hCap', dif_neg h] at hp; exact hp.elim
    have hdisjX : ∀ (S : Finset (Fin 3 → ℤ)), (S : Set (Fin 3 → ℤ)).PairwiseDisjoint
        (fun q => physIn E₁ ⁻¹' cellSet b q) := by
      intro S q _ q' _ hqq'
      rw [Function.onFun, Set.disjoint_iff]
      intro x ⟨hx, hx'⟩
      exact hqq' (hx.symm.trans hx')
    have hEeq : E = ⋃ q ∈ GoodF, Cap' q := by
      ext p
      simp only [hEdef, Set.mem_iUnion, hCap', exists_prop]
      constructor
      · rintro ⟨q, hq, hp⟩; exact ⟨q, hq, by simp only [dif_pos hq]; exact hp⟩
      · rintro ⟨q, hq, hp⟩; simp only [dif_pos hq] at hp; exact ⟨q, hq, hp⟩
    have hρE : ρ E = ∑ q ∈ GoodF, inc (Cap' q) := by
      rw [hEeq, measure_biUnion_finset
        (fun q hq q' hq' hqq' => ((hdisjX GoodF) hq hq' hqq').mono (hCap'sub q) (hCap'sub q'))
        (fun q _ => hCap'm q)]
      apply Finset.sum_congr rfl
      intro q hq
      rw [hinc, Measure.restrict_apply (hCap'm q), Set.inter_eq_left.mpr]
      intro p hp
      simp only [hCap', dif_pos hq] at hp
      exact (hCapsub q hq hp).1
    -- E₁ is the union of its heavy occupied cells
    have hE₁cover : E₁ ⊆ ⋃ q ∈ HOcc, physIn E₁ ⁻¹' cellSet b q := by
      intro p hp
      have hheavy := hp.2
      have hocc : cellIdx b (physOf p) ∈ Occ := by
        apply hOcc
        have : ENNReal.ofReal lam ≤ ρ.restrict E₀ (physOf ⁻¹' cellSet b (cellIdx b (physOf p))) := by
          simpa [heavyCells, cellSet] using hheavy
        exact (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hlam) this).ne'
      refine Set.mem_iUnion₂.mpr ⟨cellIdx b (physOf p), Finset.mem_filter.mpr ⟨hocc, hheavy⟩, ?_⟩
      show physIn E₁ p ∈ cellSet b (cellIdx b (physOf p))
      rw [physIn_eq_of_mem hp]; rfl
    have hincuniv : inc Set.univ = ∑ q ∈ HOcc, inc (physIn E₁ ⁻¹' cellSet b q) := by
      rw [← measure_biUnion_finset (hdisjX HOcc) (fun q _ => hXm q)]
      apply le_antisymm
      · calc inc Set.univ = ρ E₁ := Measure.restrict_apply_univ _
          _ ≤ ρ (E₁ ∩ ⋃ q ∈ HOcc, physIn E₁ ⁻¹' cellSet b q) := by
              apply measure_mono; intro p hp; exact ⟨hp, hE₁cover hp⟩
          _ = inc (⋃ q ∈ HOcc, physIn E₁ ⁻¹' cellSet b q) := by
              rw [hinc, Measure.restrict_apply (Finset.measurableSet_biUnion _ (fun q _ => hXm q)),
                Set.inter_comm]
      · exact measure_mono (Set.subset_univ _)
    have hsplitH : ∑ q ∈ HOcc, inc (physIn E₁ ⁻¹' cellSet b q) =
        ∑ q ∈ GoodF, inc (physIn E₁ ⁻¹' cellSet b q) + ∑ q ∈ BadF, inc (physIn E₁ ⁻¹' cellSet b q) := by
      rw [add_comm]
      exact (Finset.sum_filter_add_sum_filter_not HOcc bad _).symm
    have hgoodreal : ∀ q ∈ GoodF, (1 - c) * (inc (physIn E₁ ⁻¹' cellSet b q)).toReal ≤
        (inc (Cap' q)).toReal := by
      intro q hq
      have h := (hν q hq).2.le
      have hcap : inc (Cap' q) = inc (Cap q hq) := by simp only [hCap', dif_pos hq]
      rw [hcap]
      have := ENNReal.toReal_mono (measure_ne_top _ _) h
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at this
    have hgoodsum : (1 - c) * ∑ q ∈ GoodF, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal ≤
        (ρ.restrict E Set.univ).toReal := by
      rw [Measure.restrict_apply_univ, hρE, ENNReal.toReal_sum (fun q _ => measure_ne_top _ _),
        Finset.mul_sum]
      exact Finset.sum_le_sum hgoodreal
    have hlight := light_deletion ρ hE₀ b lam Occ hOcc
    have hE₀split : ρ E₀ ≤ ρ E₁ + ρ (E₀ \ E₁) := by
      calc ρ E₀ ≤ ρ (E₁ ∪ (E₀ \ E₁)) := measure_mono (fun p hp => by
            by_cases h : p ∈ E₁
            · exact Or.inl h
            · exact Or.inr ⟨hp, h⟩)
        _ ≤ ρ E₁ + ρ (E₀ \ E₁) := measure_union_le _ _
    have hE₁real : (ρ E₁).toReal = ∑ q ∈ GoodF, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal +
        ∑ q ∈ BadF, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal := by
      rw [← Measure.restrict_apply_univ, ← hinc, hincuniv, hsplitH,
        ENNReal.toReal_add (ENNReal.sum_ne_top.mpr fun q _ => measure_ne_top _ _)
          (ENNReal.sum_ne_top.mpr fun q _ => measure_ne_top _ _),
        ENNReal.toReal_sum (fun q _ => measure_ne_top _ _),
        ENNReal.toReal_sum (fun q _ => measure_ne_top _ _)]
    have hlightreal : (ρ (E₀ \ E₁)).toReal ≤ Occ.card * lam := by
      have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top)
        hlight
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hlam.le] at this
    have hE₀real : (ρ E₀).toReal ≤ (ρ E₁).toReal + (ρ (E₀ \ E₁)).toReal := by
      rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
      exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top _ _, measure_ne_top _ _⟩)
        hE₀split
    have h1c : 0 < 1 - c := by linarith
    have hgood_le : ∑ q ∈ GoodF, (inc (physIn E₁ ⁻¹' cellSet b q)).toReal ≤
        (ρ.restrict E Set.univ).toReal / (1 - c) := by
      rw [le_div_iff₀ h1c, mul_comm]; exact hgoodsum
    rw [Measure.restrict_apply_univ]
    linarith [hbadmass]
  · intro p hp
    simp only [hEdef, Set.mem_iUnion] at hp
    obtain ⟨q, hq, hpq⟩ := hp
    have hcell : cellIdx b (physOf p) = q := (hCapsub q hq hpq).2
    rw [hcell]
    simp only [hGdef, dif_pos hq]
    exact ⟨(hG q hq).1, (hG q hq).2.1, (hG q hq).2.2 p hpq.1 hpq.2⟩
  · intro q hq
    have hEq : E ∩ physOf ⁻¹' cellSet b q ⊆ (if h : q ∈ GoodF then Cap q h else ∅) := by
      intro p ⟨hpE, hpq⟩
      simp only [hEdef, Set.mem_iUnion] at hpE
      obtain ⟨q', hq', hpq'⟩ := hpE
      have h1 : cellIdx b (physOf p) = q' := (hCapsub q' hq' hpq').2
      have h2 : cellIdx b (physOf p) = q := hpq
      have hqq : q' = q := h1.symm.trans h2
      subst hqq
      simp only [dif_pos hq']
      exact hpq'
    rw [Measure.restrict_apply (hcellm q), Set.inter_comm] at hq ⊢
    by_cases hqG : q ∈ GoodF
    · simp only [dif_pos hqG] at hEq
      have hCapE : Cap q hqG ⊆ E ∩ physOf ⁻¹' cellSet b q := fun p hp =>
        ⟨Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨hqG, hp⟩⟩, (hCapsub q hqG hp).2⟩
      have heq : E ∩ physOf ⁻¹' cellSet b q = Cap q hqG := Set.Subset.antisymm hEq hCapE
      rw [heq]
      have hρinc : ρ (Cap q hqG) = inc (Cap q hqG) := by
        rw [hinc, Measure.restrict_apply (hCapm q hqG),
          Set.inter_eq_left.mpr (fun p hp => (hCapsub q hqG hp).1)]
      rw [hρinc]
      calc ENNReal.ofReal ((1 - c) * lam) = ENNReal.ofReal (1 - c) * ENNReal.ofReal lam :=
            ENNReal.ofReal_mul (by linarith)
        _ ≤ ENNReal.ofReal (1 - c) * inc (physIn E₁ ⁻¹' cellSet b q) := by
            gcongr; exact hincXlam q (hGoodsub hqG)
        _ ≤ inc (Cap q hqG) := (hν q hqG).2.le
    · simp only [dif_neg hqG] at hEq
      exact absurd (measure_mono_null hEq measure_empty) hq

end

end Submission.Obl.k4_scalar_tangent_isotropic_improvement
