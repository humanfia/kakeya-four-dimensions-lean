-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Parent.Qualification.ParameterPalette2, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
-- Ported from this LOT tree (oai_074): obligation o287 k4_physical_parent_potential_source,
-- file Submission/Obl/k4_physical_parent_potential_source/Qualification/ParameterPalette2.lean on the union of branches x1035 7054b970, x1065 bf5af759, x1066 90ebad49, x1037 47d17da5
-- (x1082, 2026-10-22); namespace Submission.Obl.k4_physical_parent_potential_source renamed to Submission.Obl.k4_isotropic_path_improvement.S294.Parent. Per-file credits below are the original authors'.
/- Adapted from this LOT tree, o265, session x0943, commit 4fa13b3c,
Submission/Obl/k4_staged_weak_breadth_discovery/Broad/Qualification/ParameterPalette2.lean.
All earlier source attributions below are retained. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Compatibility
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2.Interface
-- Adapted from this LOT tree, o106, branch x0352, commit 1e57792e;
-- source Submission/Obl/k4_isotropic_path_improvement/ParameterPalette2.lean.
-- Existing source attributions are preserved below; accepted scalar
-- backend modules are imported from o277 rather than copied.

/- From this LOT tree, obligation o106, session x0358, branch x0358
   at commit 4c91e1da. Original source and adaptation credits follow below. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.ParameterFloors2

/-!
# The block/cell palette and the derivative lists in version 2 (paper `tex-06`, l. 263–281)

Paper display `a05:derivative-list`: given a physical `p`-cell `W` (time, hidden coordinate,
tangential position) and a velocity bin `[V]_p = J`, the derivative `X'` to width `p` has at most
`K` options.  The argument, with every input explicit:

* blocks `B` are the `p`-bins of all seven coefficients (`blockCode`), cells `W` the `p`-bins of
  `(t, X(t), y(t))` (`cellCode`); the entry of `(B, W)` is the labelled incidence mass of the
  lines of `S` in `B` at times in `W` (`entryMass`);
* an entry *survives* when its mass is at least `p/K₁` times the full prior mass `ν(S ∩ B)`
  of its block;
* `surviving_block_count`: if every block of interest has the floor `ν(S ∩ B) ≥ f π([V]_p)`
  (`a05:parameter-floor`, lower half) and the rectangular cap at side `p` holds,
  `λ(W, [V]_p = J) ≤ K_r p^(3+d) π(J)`, then at most `K_r K₁ p^(3+d) / (p f)` blocks of velocity bin
  `J` have a surviving entry in `W`;
* `derivative_list_of_floors`: the derivative bins `⌊X'(t)/p⌋` of the incidences in surviving
  entries of `(W, J)` lie in one list of at most that many times `4K + 11` integers.

No count is assumed: the number of blocks is paid by the floors and the cap.
-/


set_option autoImplicit false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification

open MeasureTheory Set

noncomputable section

/-- The `p`-block of all seven coefficients. -/
def blockCode (p : ℝ) (c : Fin 7 → ℝ) : Fin 7 → ℤ := fun i => ⌊c i / p⌋

/-- The physical `p`-cell of an incidence: time, hidden coordinate, tangential position. -/
def cellCode (p : ℝ) (c : Fin 7 → ℝ) (t : ℝ) : ℤ × ℤ × (Fin 2 → ℤ) :=
  (⌊t / p⌋, ⌊zx c t / p⌋, fun i => ⌊zy c t i / p⌋)

/-- The velocity bin read from a block code. -/
def blockVbin (q : Fin 7 → ℤ) : Fin 2 → ℤ := ![q 4, q 6]

theorem vbin_eq_blockVbin (p : ℝ) (c : Fin 7 → ℝ) : vbin p c = blockVbin (blockCode p c) := by
  funext i
  fin_cases i <;> simp [vbin, blockVbin, blockCode]

theorem measurable_blockCode {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) (p : ℝ) : Measurable (fun l => blockCode p (c l)) := by
  apply measurable_pi_lambda
  intro i
  exact (((measurable_pi_apply i).comp hc).div_const p).floor

theorem measurable_cellCode {Λ : Type*} [MeasurableSpace Λ] {c : Λ → Fin 7 → ℝ}
    (hc : Measurable c) (p : ℝ) : Measurable (fun z : Λ × ℝ => cellCode p (c z.1) z.2) := by
  have hcomp : ∀ e : Fin 7, Measurable (fun z : Λ × ℝ => c z.1 e) :=
    fun e => (measurable_pi_apply e).comp (hc.comp measurable_fst)
  have ht : Measurable (fun z : Λ × ℝ => z.2) := measurable_snd
  have h0 := hcomp 0; have h1 := hcomp 1; have h2 := hcomp 2; have h3 := hcomp 3
  have h4 := hcomp 4; have h5 := hcomp 5; have h6 := hcomp 6
  refine (ht.div_const p).floor.prodMk (Measurable.prodMk ?_ ?_)
  · simp only [zx]
    exact (by fun_prop : Measurable (fun z : Λ × ℝ => (c z.1 0 + c z.1 1 * z.2 +
      c z.1 2 * z.2 ^ 2) / p)).floor
  · apply measurable_pi_lambda
    intro i
    fin_cases i
    · simp only [Fin.zero_eta, zy_zero]
      exact (by fun_prop : Measurable (fun z : Λ × ℝ => (c z.1 3 + c z.1 4 * z.2) / p)).floor
    · simp only [Fin.mk_one, zy_one]
      exact (by fun_prop : Measurable (fun z : Λ × ℝ => (c z.1 5 + c z.1 6 * z.2) / p)).floor

/-- The entry of a block `q` in a cell `w`: labelled incidence mass of the lines of `S` in `q`
at times in `w`. -/
def entryMass {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (S : Set Λ) (p : ℝ) (q : Fin 7 → ℤ) (w : ℤ × ℤ × (Fin 2 → ℤ)) : ENNReal :=
  (ν.prod volume) {z | z ∈ E ∧ z.1 ∈ S ∧ blockCode p (c z.1) = q ∧ cellCode p (c z.1) z.2 = w}

/-- The full prior mass of a block inside `S`. -/
def blockPrior {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ)
    (S : Set Λ) (p : ℝ) (q : Fin 7 → ℤ) : ENNReal :=
  ν {l | l ∈ S ∧ blockCode p (c l) = q}

/-- An entry survives when its mass is at least `p / K₁` times its block's prior mass. -/
def Surviving {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) (c : Λ → Fin 7 → ℝ)
    (E : Set (Λ × ℝ)) (S : Set Λ) (p K₁ : ℝ) (q : Fin 7 → ℤ) (w : ℤ × ℤ × (Fin 2 → ℤ)) :
    Prop :=
  ENNReal.ofReal (p / K₁) * blockPrior ν c S p q ≤ entryMass ν c E S p q w

open Classical in
/-- **Few blocks survive in one cell and velocity bin** (version 2). -/
theorem surviving_block_count {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ)
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    {S : Set Λ} (hS : MeasurableSet S) {p K₁ Kr f d : ℝ} (hp : 0 < p) (hK₁ : 0 < K₁)
    (hf : 0 < f) (hKr : 0 ≤ Kr) (π : (Fin 2 → ℤ) → ENNReal) (Q : Finset (Fin 7 → ℤ))
    (hfloor : ∀ q ∈ Q, ENNReal.ofReal f * π (blockVbin q) ≤ blockPrior ν c S p q)
    (w : ℤ × ℤ × (Fin 2 → ℤ)) (J : Fin 2 → ℤ) (hπ0 : π J ≠ 0) (hπtop : π J ≠ ⊤)
    (hcap : (ν.prod volume) {z | z ∈ E ∧ cellCode p (c z.1) z.2 = w ∧ vbin p (c z.1) = J} ≤
      ENNReal.ofReal (Kr * p ^ (3 + d)) * π J) :
    ((Q.filter (fun q => blockVbin q = J ∧ Surviving ν c E S p K₁ q w)).card : ℝ) ≤
      Kr * K₁ * p ^ (3 + d) / (p * f) := by
  set G := Q.filter (fun q => blockVbin q = J ∧ Surviving ν c E S p K₁ q w) with hG
  -- the entries of `G` are disjoint pieces of one capped set
  have hpiece : ∀ q, MeasurableSet
      {z : Λ × ℝ | z ∈ E ∧ z.1 ∈ S ∧ blockCode p (c z.1) = q ∧ cellCode p (c z.1) z.2 = w} := by
    intro q
    exact hE.inter ((measurable_fst hS).inter
      ((((measurable_blockCode hc p).comp measurable_fst) (measurableSet_singleton q)).inter
        ((measurable_cellCode hc p) (measurableSet_singleton w))))
  have hdisj : Set.PairwiseDisjoint (↑G : Set (Fin 7 → ℤ)) (fun q =>
      {z : Λ × ℝ | z ∈ E ∧ z.1 ∈ S ∧ blockCode p (c z.1) = q ∧ cellCode p (c z.1) z.2 = w}) := by
    intro q _ q' _ hqq'
    refine Set.disjoint_left.mpr ?_
    rintro z ⟨-, -, hq, -⟩ ⟨-, -, hq', -⟩
    exact hqq' (hq.symm.trans hq')
  have hsum : ∑ q ∈ G, entryMass ν c E S p q w ≤ ENNReal.ofReal (Kr * p ^ (3 + d)) * π J := by
    simp only [entryMass]
    rw [← measure_biUnion_finset hdisj (fun q _ => hpiece q)]
    refine le_trans (measure_mono ?_) hcap
    intro z hz
    obtain ⟨q, hq, hzq⟩ := mem_iUnion₂.mp hz
    refine ⟨hzq.1, hzq.2.2.2, ?_⟩
    rw [vbin_eq_blockVbin, hzq.2.2.1]
    exact (Finset.mem_filter.mp hq).2.1
  have hlow : ∀ q ∈ G, ENNReal.ofReal (p / K₁ * f) * π J ≤ entryMass ν c E S p q w := by
    intro q hq
    obtain ⟨hqQ, hqJ, hsurv⟩ := Finset.mem_filter.mp hq
    have hfl := hfloor q hqQ
    rw [hqJ] at hfl
    calc ENNReal.ofReal (p / K₁ * f) * π J
        = ENNReal.ofReal (p / K₁) * (ENNReal.ofReal f * π J) := by
          rw [ENNReal.ofReal_mul (by positivity), mul_assoc]
      _ ≤ ENNReal.ofReal (p / K₁) * blockPrior ν c S p q := mul_le_mul' le_rfl hfl
      _ ≤ entryMass ν c E S p q w := hsurv
  have htotal : (G.card : ENNReal) * (ENNReal.ofReal (p / K₁ * f) * π J) ≤
      ENNReal.ofReal (Kr * p ^ (3 + d)) * π J := by
    calc (G.card : ENNReal) * (ENNReal.ofReal (p / K₁ * f) * π J)
        = ∑ _q ∈ G, ENNReal.ofReal (p / K₁ * f) * π J := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ q ∈ G, entryMass ν c E S p q w := Finset.sum_le_sum hlow
      _ ≤ _ := hsum
  -- divide by `π J`
  have hcancel : (G.card : ENNReal) * ENNReal.ofReal (p / K₁ * f) ≤
      ENNReal.ofReal (Kr * p ^ (3 + d)) := by
    have h := htotal
    rw [← mul_assoc] at h
    exact (ENNReal.mul_le_mul_iff_left hπ0 hπtop).mp h
  have hreal : (G.card : ℝ) * (p / K₁ * f) ≤ Kr * p ^ (3 + d) := by
    have hpos : 0 ≤ p / K₁ * f := by positivity
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)] at hcancel
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hcancel
  have hden : 0 < p / K₁ * f := by positivity
  rw [le_div_iff₀ (by positivity : 0 < p * f)]
  have he : (G.card : ℝ) * (p * f) = (G.card : ℝ) * (p / K₁ * f) * K₁ := by
    field_simp
  rw [he]
  calc (G.card : ℝ) * (p / K₁ * f) * K₁ ≤ Kr * p ^ (3 + d) * K₁ :=
        mul_le_mul_of_nonneg_right hreal hK₁.le
    _ = Kr * K₁ * p ^ (3 + d) := by ring

/-- In one block and one time cell, the derivative `X' = c₁ + 2 c₂ t` meets at most `4K + 11`
bins of width `p`: they lie in one integer interval determined by the block and the time cell. -/
theorem derivative_bins_of_block {p K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K)
    (q : Fin 7 → ℤ) (k : ℤ)
    {c : Fin 7 → ℝ} (hcq : blockCode p c = q) (hc2 : |c 2| ≤ K) {t : ℝ}
    (ht : ⌊t / p⌋ = k) (ht1 : t ∈ Icc (0 : ℝ) 1) :
    ⌊(c 1 + 2 * c 2 * t) / p⌋ ∈ Finset.Icc
      (⌊(p * q 1 + 2 * (p * q 2) * (p * k)) / p⌋ - ⌈2 * K + 5⌉)
      (⌊(p * q 1 + 2 * (p * q 2) * (p * k)) / p⌋ + ⌈2 * K + 5⌉) := by
  have hc1 : c 1 ∈ Icc (p * q 1) (p * q 1 + p) := bin_mem_Icc hp (congrFun hcq 1)
  have hc2' : c 2 ∈ Icc (p * q 2) (p * q 2 + p) := bin_mem_Icc hp (congrFun hcq 2)
  have htk : t ∈ Icc (p * k) (p * k + p) := bin_mem_Icc hp ht
  -- |X' - X'_q| ≤ (2K + 5) p
  have hdiff : |(c 1 + 2 * c 2 * t) - (p * q 1 + 2 * (p * q 2) * (p * k))| ≤ (2 * K + 5) * p := by
    have he : (c 1 + 2 * c 2 * t) - (p * q 1 + 2 * (p * q 2) * (p * k)) =
        (c 1 - p * q 1) + 2 * (c 2 - p * q 2) * t + 2 * (p * q 2) * (t - p * k) := by ring
    rw [he]
    have hq2 : |p * q 2| ≤ K + p := by
      have h1 := abs_le.mp hc2
      rw [abs_le]; constructor <;> linarith [hc2'.1, hc2'.2]
    have e1 : |c 1 - p * q 1| ≤ p := by rw [abs_le]; constructor <;> linarith [hc1.1, hc1.2]
    have e2 : |2 * (c 2 - p * q 2) * t| ≤ 2 * p := by
      rw [abs_mul, abs_mul, abs_two, abs_of_nonneg ht1.1]
      have h : |c 2 - p * q 2| ≤ p := by rw [abs_le]; constructor <;> linarith [hc2'.1, hc2'.2]
      have := mul_le_mul h ht1.2 ht1.1 hp.le
      linarith
    have e3 : |2 * (p * q 2) * (t - p * k)| ≤ 2 * (K + p) * p := by
      rw [abs_mul, abs_mul, abs_two]
      have h : |t - p * k| ≤ p := by rw [abs_le]; constructor <;> linarith [htk.1, htk.2]
      have := mul_le_mul hq2 h (abs_nonneg _) (by linarith)
      linarith
    calc _ ≤ |c 1 - p * q 1| + |2 * (c 2 - p * q 2) * t| + |2 * (p * q 2) * (t - p * k)| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ p + 2 * p + 2 * (K + p) * p := by linarith
      _ ≤ (2 * K + 5) * p := by nlinarith
  rw [Finset.mem_Icc]
  have hscaled : |(c 1 + 2 * c 2 * t) / p - (p * q 1 + 2 * (p * q 2) * (p * k)) / p| ≤ 2 * K + 5 := by
    rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    exact hdiff
  have hfl := abs_le.mp hscaled
  have hceil := Int.le_ceil (2 * K + 5)
  constructor
  · have h1 := Int.floor_le ((p * q 1 + 2 * (p * q 2) * (p * k)) / p)
    have h2 := Int.lt_floor_add_one ((c 1 + 2 * c 2 * t) / p)
    have : ((⌊(p * q 1 + 2 * (p * q 2) * (p * k)) / p⌋ - ⌈2 * K + 5⌉ : ℤ) : ℝ) <
        (⌊(c 1 + 2 * c 2 * t) / p⌋ : ℝ) + 1 := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  · have h1 := Int.lt_floor_add_one ((p * q 1 + 2 * (p * q 2) * (p * k)) / p)
    have h2 := Int.floor_le ((c 1 + 2 * c 2 * t) / p)
    have : (⌊(c 1 + 2 * c 2 * t) / p⌋ : ℝ) <
        ((⌊(p * q 1 + 2 * (p * q 2) * (p * k)) / p⌋ + ⌈2 * K + 5⌉ : ℤ) : ℝ) + 1 := by
      push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)

open Classical in
/-- **The derivative list** (paper `a05:derivative-list`, version 2): given a cell `w` and a
velocity bin `J` of positive finite palette mass, the derivative bins `⌊X'(t)/p⌋` of all
incidences in surviving entries lie in one list of at most
`K_r K₁ p^(3+d) / (p f) · (2 ⌈2K + 5⌉ + 1)` integers. -/
theorem derivative_list_of_floors {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ)
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) {E : Set (Λ × ℝ)} (hE : MeasurableSet E)
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {S : Set Λ} (hS : MeasurableSet S)
    {p K K₁ Kr f d : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K) (hK₁ : 0 < K₁) (hf : 0 < f)
    (hKr : 0 ≤ Kr) (π : (Fin 2 → ℤ) → ENNReal) (Q : Finset (Fin 7 → ℤ))
    (hfloor : ∀ q ∈ Q, ENNReal.ofReal f * π (blockVbin q) ≤ blockPrior ν c S p q)
    (hc2 : ∀ l ∈ S, |c l 2| ≤ K)
    (w : ℤ × ℤ × (Fin 2 → ℤ)) (J : Fin 2 → ℤ) (hπ0 : π J ≠ 0) (hπtop : π J ≠ ⊤)
    (hcap : (ν.prod volume) {z | z ∈ E ∧ cellCode p (c z.1) z.2 = w ∧ vbin p (c z.1) = J} ≤
      ENNReal.ofReal (Kr * p ^ (3 + d)) * π J) :
    ∃ D : Finset ℤ, (D.card : ℝ) ≤
        Kr * K₁ * p ^ (3 + d) / (p * f) * (2 * (⌈2 * K + 5⌉ : ℝ) + 1) ∧
      ∀ z ∈ E, z.1 ∈ S → blockCode p (c z.1) ∈ Q → cellCode p (c z.1) z.2 = w →
        vbin p (c z.1) = J → Surviving ν c E S p K₁ (blockCode p (c z.1)) w →
        ⌊(c z.1 1 + 2 * c z.1 2 * z.2) / p⌋ ∈ D := by
  set G := Q.filter (fun q => blockVbin q = J ∧ Surviving ν c E S p K₁ q w) with hG
  have hcount := surviving_block_count ν hc hE hS hp hK₁ hf hKr π Q hfloor w J hπ0 hπtop hcap
  rw [← hG] at hcount
  set R : ℤ := ⌈2 * K + 5⌉ with hRdef
  let center : (Fin 7 → ℤ) → ℤ := fun q =>
    ⌊(p * q 1 + 2 * (p * q 2) * (p * w.1)) / p⌋
  refine ⟨G.biUnion (fun q => Finset.Icc (center q - R) (center q + R)), ?_, ?_⟩
  · have hR0 : (0 : ℝ) ≤ R := by
      have := Int.le_ceil (2 * K + 5)
      have h5 : (0 : ℝ) ≤ 2 * K + 5 := by linarith
      exact_mod_cast (show (0 : ℤ) ≤ R from by exact_mod_cast h5.trans this)
    have hcard : ((G.biUnion (fun q => Finset.Icc (center q - R) (center q + R))).card : ℝ) ≤
        (G.card : ℝ) * (2 * (R : ℝ) + 1) := by
      have h1 := Finset.card_biUnion_le (s := G) (t := fun q => Finset.Icc (center q - R) (center q + R))
      have h2 : ∀ q ∈ G, ((Finset.Icc (center q - R) (center q + R)).card : ℝ) = 2 * (R : ℝ) + 1 := by
        intro q _
        rw [Int.card_Icc]
        have : (center q + R + 1 - (center q - R)) = 2 * R + 1 := by ring
        rw [this]
        have hR0' : (0 : ℤ) ≤ R := by exact_mod_cast hR0
        have hnn : (0 : ℤ) ≤ 2 * R + 1 := by omega
        have e : (((2 * R + 1).toNat : ℕ) : ℝ) = ((2 * R + 1 : ℤ) : ℝ) := by
          rw [← Int.cast_natCast, Int.toNat_of_nonneg hnn]
        rw [e]; push_cast; ring
      calc ((G.biUnion (fun q => Finset.Icc (center q - R) (center q + R))).card : ℝ)
          ≤ ((∑ q ∈ G, (Finset.Icc (center q - R) (center q + R)).card : ℕ) : ℝ) := by
            exact_mod_cast h1
        _ = ∑ q ∈ G, (((Finset.Icc (center q - R) (center q + R)).card : ℕ) : ℝ) := by
            push_cast; rfl
        _ = ∑ _q ∈ G, (2 * (R : ℝ) + 1) := Finset.sum_congr rfl h2
        _ = (G.card : ℝ) * (2 * (R : ℝ) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    calc _ ≤ (G.card : ℝ) * (2 * (R : ℝ) + 1) := hcard
      _ ≤ Kr * K₁ * p ^ (3 + d) / (p * f) * (2 * (R : ℝ) + 1) :=
          mul_le_mul_of_nonneg_right hcount (by linarith)
  · intro z hz hzS hzQ hzw hzJ hsurv
    have hqG : blockCode p (c z.1) ∈ G := by
      refine Finset.mem_filter.mpr ⟨hzQ, ?_, hsurv⟩
      rw [← vbin_eq_blockVbin]; exact hzJ
    refine Finset.mem_biUnion.mpr ⟨blockCode p (c z.1), hqG, ?_⟩
    have htime : ⌊z.2 / p⌋ = w.1 := by rw [← hzw]; rfl
    exact derivative_bins_of_block hp hp1 hK (blockCode p (c z.1)) w.1 rfl (hc2 z.1 hzS) htime
      (hunit hz).2

/-! ### Deleting the entries that do not survive -/

theorem floor_mem_Icc_of_close {a b A : ℝ} (h : |a - b| ≤ A) :
    ⌊a⌋ ∈ Finset.Icc (⌊b⌋ - (⌈A⌉ + 1)) (⌊b⌋ + (⌈A⌉ + 1)) := by
  have hab := abs_le.mp h
  have hA := Int.le_ceil A
  have h1 := Int.floor_le a
  have h2 := Int.lt_floor_add_one a
  have h3 := Int.floor_le b
  have h4 := Int.lt_floor_add_one b
  rw [Finset.mem_Icc]
  constructor
  · have : ((⌊b⌋ - (⌈A⌉ + 1) : ℤ) : ℝ) < (⌊a⌋ : ℝ) + 1 := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)
  · have : (⌊a⌋ : ℝ) < ((⌊b⌋ + (⌈A⌉ + 1) : ℤ) : ℝ) + 1 := by push_cast; linarith
    exact Int.lt_add_one_iff.mp (by exact_mod_cast this)

/-- The index of the initial position `y₀ i` and of the velocity `V i` among the coefficients. -/
def yIdx : Fin 2 → Fin 7 := ![3, 5]
def vIdx : Fin 2 → Fin 7 := ![4, 6]

theorem zy_eq_idx (c : Fin 7 → ℝ) (t : ℝ) (i : Fin 2) : zy c t i = c (yIdx i) + c (vIdx i) * t := by
  fin_cases i <;> simp [yIdx, vIdx]

/-- The cells met by the lines of the block `q` (coefficients bounded by `K`) at times in `[0,1]`. -/
def blockCells (p K : ℝ) (q : Fin 7 → ℤ) : Finset (ℤ × ℤ × (Fin 2 → ℤ)) :=
  (Finset.range (⌊1 / p⌋₊ + 1)).biUnion fun k =>
    ((Finset.Icc (⌊(p * q 0 + p * q 1 * ((k : ℝ) * p) + p * q 2 * ((k : ℝ) * p) ^ 2) / p⌋ -
        (⌈6 + 3 * K⌉ + 1))
      (⌊(p * q 0 + p * q 1 * ((k : ℝ) * p) + p * q 2 * ((k : ℝ) * p) ^ 2) / p⌋ +
        (⌈6 + 3 * K⌉ + 1))) ×ˢ
      (Fintype.piFinset fun i : Fin 2 =>
        Finset.Icc (⌊(p * q (yIdx i) + (k : ℝ) * p * (p * q (vIdx i))) / p⌋ - (⌈2 + K⌉ + 1))
          (⌊(p * q (yIdx i) + (k : ℝ) * p * (p * q (vIdx i))) / p⌋ + (⌈2 + K⌉ + 1)))).image
      fun xy => ((k : ℤ), xy.1, xy.2)

theorem cellCode_mem_blockCells {p K : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K)
    {c : Fin 7 → ℝ} (hcK : ∀ e, |c e| ≤ K) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    cellCode p c t ∈ blockCells p K (blockCode p c) := by
  set q := blockCode p c with hq
  have hbin : ∀ e, c e ∈ Icc (p * q e) (p * q e + p) := fun e => bin_mem_Icc hp rfl
  have hqK : ∀ e, |p * q e| ≤ K + p := by
    intro e
    have h1 := abs_le.mp (hcK e)
    have h2 := hbin e
    rw [abs_le]; constructor <;> linarith [h2.1, h2.2]
  set k : ℕ := ⌊t / p⌋₊ with hk
  have hkle : (k : ℝ) * p ≤ t := by
    have := Nat.floor_le (div_nonneg ht.1 hp.le)
    calc (k : ℝ) * p ≤ t / p * p := mul_le_mul_of_nonneg_right this hp.le
      _ = t := div_mul_cancel₀ _ hp.ne'
  have hklt : t < (k : ℝ) * p + p := by
    have h2 : t / p < (k : ℝ) + 1 := Nat.lt_floor_add_one (t / p)
    have h3 := (div_lt_iff₀ hp).mp h2
    linarith
  have hkM : k < ⌊1 / p⌋₊ + 1 := by
    have : k ≤ ⌊1 / p⌋₊ := Nat.floor_mono (div_le_div_of_nonneg_right ht.2 hp.le)
    omega
  have hfloor_t : ⌊t / p⌋ = (k : ℤ) := by
    rw [hk]; exact (Int.natCast_floor_eq_floor (div_nonneg ht.1 hp.le)).symm
  set s : ℝ := (k : ℝ) * p with hs
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := hkle.trans ht.2
  have hts : |t - s| ≤ p := by rw [abs_le]; constructor <;> linarith
  -- the hidden coordinate
  have hX : |zx c t / p - (p * q 0 + p * q 1 * s + p * q 2 * s ^ 2) / p| ≤ 6 + 3 * K := by
    rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp]
    have he : zx c t - (p * q 0 + p * q 1 * s + p * q 2 * s ^ 2) =
        (c 0 - p * q 0) + (c 1 - p * q 1) * t + (c 2 - p * q 2) * t ^ 2 +
          (p * q 1 * (t - s) + p * q 2 * ((t - s) * (t + s))) := by
      simp only [zx]; ring
    rw [he]
    have e0 : |c 0 - p * q 0| ≤ p := by rw [abs_le]; constructor <;> linarith [(hbin 0).1, (hbin 0).2]
    have e1 : |(c 1 - p * q 1) * t| ≤ p := by
      rw [abs_mul, abs_of_nonneg ht.1]
      have h : |c 1 - p * q 1| ≤ p := by rw [abs_le]; constructor <;> linarith [(hbin 1).1, (hbin 1).2]
      nlinarith [abs_nonneg (c 1 - p * q 1), ht.2]
    have e2 : |(c 2 - p * q 2) * t ^ 2| ≤ p := by
      rw [abs_mul, abs_of_nonneg (sq_nonneg t)]
      have h : |c 2 - p * q 2| ≤ p := by rw [abs_le]; constructor <;> linarith [(hbin 2).1, (hbin 2).2]
      have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
      nlinarith [abs_nonneg (c 2 - p * q 2), sq_nonneg t]
    have e3 : |p * q 1 * (t - s)| ≤ (K + p) * p := by
      rw [abs_mul]; exact mul_le_mul (hqK 1) hts (abs_nonneg _) (by linarith)
    have e4 : |p * q 2 * ((t - s) * (t + s))| ≤ (K + p) * (p * 2) := by
      rw [abs_mul, abs_mul (t - s)]
      have hsum : |t + s| ≤ 2 := by
        rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
      exact mul_le_mul (hqK 2) (mul_le_mul hts hsum (abs_nonneg _) hp.le) (by positivity)
        (by linarith)
    calc _ ≤ |c 0 - p * q 0| + |(c 1 - p * q 1) * t| + |(c 2 - p * q 2) * t ^ 2| +
          (|p * q 1 * (t - s)| + |p * q 2 * ((t - s) * (t + s))|) :=
          (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans
            (add_le_add (abs_add_le _ _) le_rfl)) (abs_add_le _ _))
      _ ≤ p + p + p + ((K + p) * p + (K + p) * (p * 2)) := by linarith
      _ ≤ (6 + 3 * K) * p := by nlinarith
  -- the tangential position
  have hY : ∀ i, |zy c t i / p - (p * q (yIdx i) + s * (p * q (vIdx i))) / p| ≤ 2 + K := by
    intro i
    rw [← sub_div, abs_div, abs_of_pos hp, div_le_iff₀ hp, zy_eq_idx]
    have he : c (yIdx i) + c (vIdx i) * t - (p * q (yIdx i) + s * (p * q (vIdx i))) =
        (c (yIdx i) - p * q (yIdx i)) + (t - s) * c (vIdx i) + s * (c (vIdx i) - p * q (vIdx i)) := by
      ring
    rw [he]
    have e0 : |c (yIdx i) - p * q (yIdx i)| ≤ p := by
      rw [abs_le]; constructor <;> linarith [(hbin (yIdx i)).1, (hbin (yIdx i)).2]
    have e1 : |(t - s) * c (vIdx i)| ≤ p * K := by
      rw [abs_mul]; exact mul_le_mul hts (hcK _) (abs_nonneg _) hp.le
    have e2 : |s * (c (vIdx i) - p * q (vIdx i))| ≤ p := by
      rw [abs_mul, abs_of_nonneg hs0]
      have h : |c (vIdx i) - p * q (vIdx i)| ≤ p := by
        rw [abs_le]; constructor <;> linarith [(hbin (vIdx i)).1, (hbin (vIdx i)).2]
      nlinarith [abs_nonneg (c (vIdx i) - p * q (vIdx i))]
    calc _ ≤ |c (yIdx i) - p * q (yIdx i)| + |(t - s) * c (vIdx i)| +
          |s * (c (vIdx i) - p * q (vIdx i))| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ p + p * K + p := by linarith
      _ = (2 + K) * p := by ring
  refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_range.mpr hkM, Finset.mem_image.mpr
    ⟨(⌊zx c t / p⌋, fun i => ⌊zy c t i / p⌋), ?_, ?_⟩⟩
  · refine Finset.mem_product.mpr ⟨floor_mem_Icc_of_close hX, ?_⟩
    exact Fintype.mem_piFinset.mpr fun i => floor_mem_Icc_of_close (hY i)
  · simp only [cellCode, hfloor_t]

theorem card_blockCells_le (p K : ℝ) (q : Fin 7 → ℤ) :
    (blockCells p K q).card ≤ (⌊1 / p⌋₊ + 1) *
      ((2 * (⌈6 + 3 * K⌉ + 1) + 1).toNat * ((2 * (⌈2 + K⌉ + 1) + 1).toNat) ^ 2) := by
  unfold blockCells
  refine (Finset.card_biUnion_le).trans ?_
  have hk : ∀ k ∈ Finset.range (⌊1 / p⌋₊ + 1),
      (((Finset.Icc (⌊(p * q 0 + p * q 1 * ((k : ℝ) * p) + p * q 2 * ((k : ℝ) * p) ^ 2) / p⌋ -
        (⌈6 + 3 * K⌉ + 1))
      (⌊(p * q 0 + p * q 1 * ((k : ℝ) * p) + p * q 2 * ((k : ℝ) * p) ^ 2) / p⌋ +
        (⌈6 + 3 * K⌉ + 1))) ×ˢ
      (Fintype.piFinset fun i : Fin 2 =>
        Finset.Icc (⌊(p * q (yIdx i) + (k : ℝ) * p * (p * q (vIdx i))) / p⌋ - (⌈2 + K⌉ + 1))
          (⌊(p * q (yIdx i) + (k : ℝ) * p * (p * q (vIdx i))) / p⌋ + (⌈2 + K⌉ + 1)))).image
      fun xy => ((k : ℤ), xy.1, xy.2)).card ≤
        (2 * (⌈6 + 3 * K⌉ + 1) + 1).toNat * ((2 * (⌈2 + K⌉ + 1) + 1).toNat) ^ 2 := by
    intro k _
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_product, Fintype.card_piFinset, Fin.prod_univ_two, Int.card_Icc,
      Int.card_Icc, Int.card_Icc]
    have e1 : ∀ x R : ℤ, x + R + 1 - (x - R) = 2 * R + 1 := fun x R => by ring
    rw [e1, e1, e1, sq]
  calc ∑ k ∈ Finset.range (⌊1 / p⌋₊ + 1), _ ≤
      ∑ _k ∈ Finset.range (⌊1 / p⌋₊ + 1),
        (2 * (⌈6 + 3 * K⌉ + 1) + 1).toNat * ((2 * (⌈2 + K⌉ + 1) + 1).toNat) ^ 2 :=
        Finset.sum_le_sum hk
    _ = _ := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Deleting the entries that do not survive** costs at most `C / K₁` of the prior mass of `S`,
`C = 2 (2 (⌈6 + 3K⌉ + 1) + 1) (2 (⌈2 + K⌉ + 1) + 1)²` (each block meets at most `C / p` cells). -/
theorem nonsurviving_entries_cost {Λ : Type*} [MeasurableSpace Λ] (ν : Measure Λ) [SFinite ν]
    {c : Λ → Fin 7 → ℝ} (hc : Measurable c) {E : Set (Λ × ℝ)}
    (hunit : E ⊆ univ ×ˢ Icc (0 : ℝ) 1) {S : Set Λ} (hS : MeasurableSet S)
    {p K K₁ : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) (hK : 0 ≤ K) (hK₁ : 0 < K₁)
    (hcoeff : ∀ l ∈ S, ∀ e, |c l e| ≤ K) :
    (ν.prod volume) {z | z ∈ E ∧ z.1 ∈ S ∧
        ¬ Surviving ν c E S p K₁ (blockCode p (c z.1)) (cellCode p (c z.1) z.2)} ≤
      ENNReal.ofReal (2 * (((2 * (⌈6 + 3 * K⌉ + 1) + 1).toNat * ((2 * (⌈2 + K⌉ + 1) + 1).toNat) ^ 2 :
        ℕ) : ℝ) / K₁) * ν S := by
  classical
  set C₀ : ℕ := (2 * (⌈6 + 3 * K⌉ + 1) + 1).toNat * ((2 * (⌈2 + K⌉ + 1) + 1).toNat) ^ 2 with hC₀
  set M : ℕ := ⌊1 / p⌋₊ + 1 with hM
  -- the deleted set, block by block
  let piece : (Fin 7 → ℤ) → (ℤ × ℤ × (Fin 2 → ℤ)) → Set (Λ × ℝ) := fun q w =>
    {z | z ∈ E ∧ z.1 ∈ S ∧ blockCode p (c z.1) = q ∧ cellCode p (c z.1) z.2 = w}
  have hcover : {z | z ∈ E ∧ z.1 ∈ S ∧
      ¬ Surviving ν c E S p K₁ (blockCode p (c z.1)) (cellCode p (c z.1) z.2)} ⊆
      ⋃ q : Fin 7 → ℤ, ⋃ w ∈ (blockCells p K q).filter (fun w => ¬ Surviving ν c E S p K₁ q w),
        piece q w := by
    intro z hz
    refine mem_iUnion.mpr ⟨blockCode p (c z.1), mem_iUnion₂.mpr ⟨cellCode p (c z.1) z.2, ?_, ?_⟩⟩
    · exact Finset.mem_filter.mpr ⟨cellCode_mem_blockCells hp hp1 hK (hcoeff z.1 hz.2.1)
        (hunit hz.1).2, hz.2.2⟩
    · exact ⟨hz.1, hz.2.1, rfl, rfl⟩
  have hblock : ∀ q : Fin 7 → ℤ,
      (ν.prod volume) (⋃ w ∈ (blockCells p K q).filter (fun w => ¬ Surviving ν c E S p K₁ q w),
        piece q w) ≤ ENNReal.ofReal (2 * (C₀ : ℝ) / K₁) * blockPrior ν c S p q := by
    intro q
    calc (ν.prod volume) (⋃ w ∈ (blockCells p K q).filter (fun w => ¬ Surviving ν c E S p K₁ q w),
          piece q w)
        ≤ ∑ w ∈ (blockCells p K q).filter (fun w => ¬ Surviving ν c E S p K₁ q w),
            (ν.prod volume) (piece q w) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _w ∈ (blockCells p K q).filter (fun w => ¬ Surviving ν c E S p K₁ q w),
            ENNReal.ofReal (p / K₁) * blockPrior ν c S p q := by
          apply Finset.sum_le_sum
          intro w hw
          have hns := (Finset.mem_filter.mp hw).2
          simp only [Surviving, not_le] at hns
          exact hns.le
      _ ≤ ∑ _w ∈ blockCells p K q, ENNReal.ofReal (p / K₁) * blockPrior ν c S p q :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = ((blockCells p K q).card : ENNReal) * (ENNReal.ofReal (p / K₁) * blockPrior ν c S p q) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ENNReal.ofReal (2 * (C₀ : ℝ) / K₁) * blockPrior ν c S p q := by
          rw [← mul_assoc]
          apply mul_le_mul' _ le_rfl
          have hcard := card_blockCells_le p K q
          have hreal : ((blockCells p K q).card : ℝ) * (p / K₁) ≤ 2 * (C₀ : ℝ) / K₁ := by
            have h1 : ((blockCells p K q).card : ℝ) ≤ (M : ℝ) * (C₀ : ℝ) := by exact_mod_cast hcard
            have hMp : (M : ℝ) * p ≤ 2 := by
              have hfl : (⌊1 / p⌋₊ : ℝ) ≤ 1 / p := Nat.floor_le (by positivity)
              have : (⌊1 / p⌋₊ : ℝ) * p ≤ 1 := by
                calc (⌊1 / p⌋₊ : ℝ) * p ≤ 1 / p * p := mul_le_mul_of_nonneg_right hfl hp.le
                  _ = 1 := by field_simp
              rw [hM]; push_cast; linarith
            have hC0 : (0 : ℝ) ≤ C₀ := Nat.cast_nonneg _
            calc ((blockCells p K q).card : ℝ) * (p / K₁) ≤ (M : ℝ) * (C₀ : ℝ) * (p / K₁) :=
                  mul_le_mul_of_nonneg_right h1 (by positivity)
              _ = ((M : ℝ) * p) * (C₀ : ℝ) / K₁ := by ring
              _ ≤ 2 * (C₀ : ℝ) / K₁ := by
                  apply div_le_div_of_nonneg_right _ hK₁.le
                  exact mul_le_mul_of_nonneg_right hMp hC0
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          exact ENNReal.ofReal_le_ofReal hreal
  have hdisj : Pairwise (Function.onFun Disjoint fun q : Fin 7 → ℤ => {l | l ∈ S ∧ blockCode p (c l) = q}) := by
    intro q q' hqq'
    refine Set.disjoint_left.mpr ?_
    rintro l ⟨-, hq⟩ ⟨-, hq'⟩
    exact hqq' (hq.symm.trans hq')
  have hmeas : ∀ q : Fin 7 → ℤ, MeasurableSet {l | l ∈ S ∧ blockCode p (c l) = q} :=
    fun q => hS.inter ((measurable_blockCode hc p) (measurableSet_singleton q))
  have hunion : (⋃ q : Fin 7 → ℤ, {l | l ∈ S ∧ blockCode p (c l) = q}) = S := by
    ext l; simp
  calc (ν.prod volume) {z | z ∈ E ∧ z.1 ∈ S ∧
        ¬ Surviving ν c E S p K₁ (blockCode p (c z.1)) (cellCode p (c z.1) z.2)}
      ≤ (ν.prod volume) (⋃ q : Fin 7 → ℤ, ⋃ w ∈ (blockCells p K q).filter
          (fun w => ¬ Surviving ν c E S p K₁ q w), piece q w) := measure_mono hcover
    _ ≤ ∑' q : Fin 7 → ℤ, (ν.prod volume) (⋃ w ∈ (blockCells p K q).filter
          (fun w => ¬ Surviving ν c E S p K₁ q w), piece q w) := measure_iUnion_le _
    _ ≤ ∑' q : Fin 7 → ℤ, ENNReal.ofReal (2 * (C₀ : ℝ) / K₁) * blockPrior ν c S p q :=
        ENNReal.tsum_le_tsum hblock
    _ = ENNReal.ofReal (2 * (C₀ : ℝ) / K₁) * ∑' q : Fin 7 → ℤ, blockPrior ν c S p q :=
        ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (2 * (C₀ : ℝ) / K₁) * ν S := by
        congr 1
        simp only [blockPrior]
        rw [← measure_iUnion hdisj hmeas, hunion]

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Parent.Qualification.Jets2
