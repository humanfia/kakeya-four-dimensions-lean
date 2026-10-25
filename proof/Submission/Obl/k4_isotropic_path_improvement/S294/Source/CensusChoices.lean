-- Ported from this LOT tree: o294 k4_physical_row_packet_source (sessions x1082, x1088, x1095, x1096 and others), module Submission.Obl.k4_physical_row_packet_source.Source.CensusChoices, prefix renamed to Submission.Obl.k4_isotropic_path_improvement.S294 (x1078).
/- The census parameters at a sample (session x1088).

Explicit choices for every free parameter of x1065's ancestor census
(`BroadMultiscaleCoreSource.exists_multiscale_ancestor_census_source`, through
`Source.RootCensusPackage.root_census_package`), from the core constant `K`, the path factor `κ`,
`N`, `δ₀ L`, the broad residual's radius `rF` and the grid `m`:
* `geomOf K N δ₀ L = max (max K (N^(2 δ₀ L))) (96 coreRowK₀)` (`Kgeom`);
* `stripExpOf` (`w`, `6 κ³ N^(2δ₀L)/rF ≤ Kgeom^w ≤ Kgeom · 6 κ³ N^(2δ₀L)/rF`), width `Kgeom^-w`;
* `rowExpOf R = 2R + 32` (`t`), `θrow = Kgeom^-t`;
* `layerQOf w R = ⌈w/(3R+66)⌉` (`qc`), layer constant `Kgeom^(3R+66)`;
* `gapExpOf` (one gap power for consecutive levels, `2 N^((1/m + 2δ₀) L) ≤ Kgeom^gap`);
* `censusKOf Kgeom R J w t gap = Kgeom^(3R + gp + gap + 83)` (ONE census constant for the root's
  MK4 occupancy and for the children), `censusGp` its `gp`;
* `listLenOf m δ₀ L N X = ⌈m (2δ₀ + logb N X / L)⌉` (a list deep enough for
  `δ(r(a + nn))/δ(r a) ≤ 2/X`);
* `deepPowerOf R J = (3R+66)(4J+15) + R + 10` (the margin power of `hdeep`).
This file: the definitions and their numeric facts. -/
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.GridMono
import Submission.Obl.k4_isotropic_path_improvement.S294.Source.LevelRatios
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.CoreLipschitz
import Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource.Broad.Gradient.RenewalCells

set_option linter.unusedVariables false

namespace Submission.Obl.k4_isotropic_path_improvement.S294.Source

open Submission.Obl.k4_isotropic_path_improvement.S294.Parent.ParentSource

noncomputable section

/-- The least power of `X > 1` above `A`. -/
def logCeil (X A : ℝ) : ℕ := ⌈Real.logb X A⌉₊

theorem logCeil_spec {X A : ℝ} (hX : 1 < X) (hA : 1 ≤ A) :
    A ≤ X ^ logCeil X A ∧ X ^ logCeil X A ≤ X * A := by
  have hX0 : 0 < X := by linarith
  have hA0 : 0 < A := by linarith
  have hlog : 0 ≤ Real.logb X A := Real.logb_nonneg hX hA
  have hpow : X ^ Real.logb X A = A := Real.rpow_logb hX0 hX.ne' hA0
  have hcast : X ^ logCeil X A = X ^ ((logCeil X A : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
  constructor
  · rw [hcast]
    calc A = X ^ Real.logb X A := hpow.symm
      _ ≤ X ^ ((logCeil X A : ℕ) : ℝ) := Real.rpow_le_rpow_of_exponent_le hX.le (Nat.le_ceil _)
  · rw [hcast]
    have h1 : ((logCeil X A : ℕ) : ℝ) ≤ Real.logb X A + 1 := (Nat.ceil_lt_add_one hlog).le
    calc X ^ ((logCeil X A : ℕ) : ℝ) ≤ X ^ (Real.logb X A + 1) :=
          Real.rpow_le_rpow_of_exponent_le hX.le h1
      _ = X * A := by rw [Real.rpow_add hX0, hpow, Real.rpow_one]; ring

/-- `Kgeom`. -/
def geomOf (K N δ₀ L : ℝ) : ℝ := max (max K (N ^ (2 * δ₀ * L))) (96 * coreRowK₀)

/-- The strip exponent `w`. -/
def stripExpOf (Kgeom κ N δ₀ L rF : ℝ) : ℕ :=
  logCeil Kgeom (6 * κ ^ 3 * N ^ (2 * δ₀ * L) / rF)

/-- The row exponent `t`. -/
def rowExpOf (R : ℕ) : ℕ := 2 * R + 32

/-- The layer exponent `qc = ⌈w/(3R+66)⌉`. -/
def layerQOf (w R : ℕ) : ℕ := (w + (3 * R + 65)) / (3 * R + 66)

/-- The gap power of consecutive levels. -/
def gapExpOf (Kgeom N δ₀ L : ℝ) (m : ℕ) : ℕ :=
  logCeil Kgeom (2 * N ^ ((1 / (m : ℝ) + 2 * δ₀) * L))

/-- The census's `gp`. -/
def censusGp (R J w t : ℕ) : ℕ := ((3 * R + 58) + 8) * J + w + t * ⌈coreRowC₀⌉₊ + 1

/-- The census constant. -/
def censusKOf (Kgeom : ℝ) (R J w t gap : ℕ) : ℝ :=
  Kgeom ^ (3 * R + censusGp R J w t + gap + 83)

/-- The list length for `δ(r(a + nn))/δ(r a) ≤ 2/X`. -/
def listLenOf (m : ℕ) (δ₀ L N X : ℝ) : ℕ := ⌈(m : ℝ) * (2 * δ₀ + Real.logb N X / L)⌉₊

/-- The margin power of `hdeep`. -/
def deepPowerOf (R J : ℕ) : ℕ := (3 * R + 66) * (4 * J + 15) + R + 10

section Facts

theorem geomOf_ge {K N δ₀ L : ℝ} :
    K ≤ geomOf K N δ₀ L ∧ N ^ (2 * δ₀ * L) ≤ geomOf K N δ₀ L ∧
      96 * coreRowK₀ ≤ geomOf K N δ₀ L :=
  ⟨(le_max_left _ _).trans (le_max_left _ _), (le_max_right _ _).trans (le_max_left _ _),
    le_max_right _ _⟩

theorem layerQ_spec (w R : ℕ) :
    w ≤ (3 * R + 66) * layerQOf w R ∧ (3 * R + 66) * layerQOf w R ≤ w + (3 * R + 65) := by
  have h0 : 0 < 3 * R + 66 := by omega
  have hdm := Nat.div_add_mod (w + (3 * R + 65)) (3 * R + 66)
  have hmod := Nat.mod_lt (w + (3 * R + 65)) h0
  unfold layerQOf
  constructor
  · nlinarith
  · calc (3 * R + 66) * ((w + (3 * R + 65)) / (3 * R + 66))
        ≤ (3 * R + 66) * ((w + (3 * R + 65)) / (3 * R + 66)) +
          (w + (3 * R + 65)) % (3 * R + 66) := Nat.le_add_right _ _
      _ = w + (3 * R + 65) := hdm

/-- One thickness against another: `δ(r) ≤ 2 N^(r' - r) δ(r')`. -/
theorem delta_le_two_rpow_mul {N r r' : ℝ} (hN : 0 < N) :
    O204.Split.δ N r ≤ 2 * N ^ (r' - r) * O204.Split.δ N r' := by
  have h1 := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN r).2
  have h2 := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hN r').1
  calc O204.Split.δ N r ≤ 2 * N ^ (-r) := h1
    _ = 2 * N ^ (r' - r) * N ^ (-r') := by
        rw [mul_assoc, ← Real.rpow_add hN]; ring_nf
    _ ≤ 2 * N ^ (r' - r) * O204.Split.δ N r' :=
        mul_le_mul_of_nonneg_left h2 (by positivity)

/-- **Consecutive levels** differ by at most `2 N^((1/m + 2δ₀) L)` in thickness. -/
theorem delta_step_le {N L δ₀ : ℝ} {m : ℕ} {s r : ℕ → ℝ} (hN : 1 < N) (hm : 0 < m)
    (hs : ∀ i, s i = ((i : ℝ) + 1) / m) (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L)
    {l : ℕ} (hl : l + 1 < m) :
    O204.Split.δ N (r l) ≤ 2 * N ^ ((1 / (m : ℝ) + 2 * δ₀) * L) * O204.Split.δ N (r (l + 1)) := by
  have hNp : 0 < N := by linarith
  have h1 := (abs_le.mp (hr l (by omega))).1
  have h2 := (abs_le.mp (hr (l + 1) hl)).2
  have hsd : s (l + 1) - s l = 1 / (m : ℝ) := by
    rw [hs, hs]; push_cast; ring
  have e : s (l + 1) * L - s l * L = 1 / (m : ℝ) * L := by rw [← sub_mul, hsd]
  have hexp : r (l + 1) - r l ≤ (1 / (m : ℝ) + 2 * δ₀) * L := by linarith
  calc O204.Split.δ N (r l) ≤ 2 * N ^ (r (l + 1) - r l) * O204.Split.δ N (r (l + 1)) :=
        delta_le_two_rpow_mul hNp
    _ ≤ 2 * N ^ ((1 / (m : ℝ) + 2 * δ₀) * L) * O204.Split.δ N (r (l + 1)) := by
        have := O204.Tangent.δ_pos N (r (l + 1))
        gcongr
        exact hN.le

/-- **A deep enough list**: `δ(r(a + nn))/δ(r a) ≤ 2/X`. -/
theorem list_last_le {N L δ₀ X : ℝ} {m : ℕ} {s r : ℕ → ℝ} (hN : 1 < N) (hL : 0 < L)
    (hm : 0 < m) (hX : 0 < X) (hs : ∀ i, s i = ((i : ℝ) + 1) / m)
    (hr : ∀ i, i < m → |r i - s i * L| ≤ δ₀ * L) {a nn : ℕ} (hann : a + nn < m)
    (hnn : (m : ℝ) * (2 * δ₀ + Real.logb N X / L) ≤ nn) :
    O204.Split.δ N (r (a + nn)) / O204.Split.δ N (r a) ≤ 2 / X := by
  have hNp : 0 < N := by linarith
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 := (abs_le.mp (hr a (by omega))).2
  have h2 := (abs_le.mp (hr (a + nn) hann)).1
  have hsd : s (a + nn) - s a = (nn : ℝ) / m := by
    rw [hs, hs]; push_cast; ring
  -- `logb N X ≤ r(a + nn) - r a`
  have hnn' : 2 * δ₀ + Real.logb N X / L ≤ (nn : ℝ) / m := by
    rw [le_div_iff₀ hmR]; linarith
  have hlogX : Real.logb N X ≤ ((nn : ℝ) / m - 2 * δ₀) * L := by
    have := (div_le_iff₀ hL).mp (by linarith : Real.logb N X / L ≤ (nn : ℝ) / m - 2 * δ₀)
    linarith
  have hgap : Real.logb N X ≤ r (a + nn) - r a := by nlinarith
  have hδa := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (r a)).1
  have hδb := (Submission.Obl.k4_clean_cover_graph_atlas.gδ_two_sided hNp (r (a + nn))).2
  have hδa0 : 0 < O204.Split.δ N (r a) := O204.Tangent.δ_pos _ _
  rw [div_le_div_iff₀ hδa0 hX]
  have hXpow : N ^ Real.logb N X = X := Real.rpow_logb hNp hN.ne' hX
  calc O204.Split.δ N (r (a + nn)) * X ≤ 2 * N ^ (-r (a + nn)) * N ^ Real.logb N X := by
        rw [hXpow]; exact mul_le_mul_of_nonneg_right hδb hX.le
    _ = 2 * (N ^ (Real.logb N X - r (a + nn) + r a) * N ^ (-r a)) := by
        rw [← Real.rpow_add hNp]; rw [mul_assoc, ← Real.rpow_add hNp]; ring_nf
    _ ≤ 2 * (N ^ (0 : ℝ) * N ^ (-r a)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow_of_exponent_le hN.le (by linarith)) (by positivity)
    _ = 2 * N ^ (-r a) := by rw [Real.rpow_zero, one_mul]
    _ ≤ 2 * O204.Split.δ N (r a) := mul_le_mul_of_nonneg_left hδa (by norm_num)

/-- The census constant is at least `1` and at least `Kgeom^3`. -/
theorem censusK_ge {Kgeom : ℝ} (hK : 1 ≤ Kgeom) (R J w t gap : ℕ) :
    1 ≤ censusKOf Kgeom R J w t gap ∧ Kgeom ^ 3 ≤ censusKOf Kgeom R J w t gap := by
  unfold censusKOf
  exact ⟨one_le_pow₀ hK, pow_le_pow_right₀ hK (by omega)⟩

/-- **The strip choice**: `A ≤ Kgeom^w ≤ Kgeom A` for `A = 6 κ³ N^(2δ₀L)/rF`, and the strip
condition of the census for `width = (Kgeom^w)⁻¹`. -/
theorem strip_spec {Kgeom κ N δ₀ L rF : ℝ} (hK : 1 < Kgeom) (hκ : 1 ≤ κ) (hN : 1 ≤ N)
    (hδL : 0 ≤ 2 * δ₀ * L) (hrF : 0 < rF) (hrF1 : rF ≤ 1) :
    6 * κ ^ 3 * N ^ (2 * δ₀ * L) / rF ≤ Kgeom ^ stripExpOf Kgeom κ N δ₀ L rF ∧
      Kgeom ^ stripExpOf Kgeom κ N δ₀ L rF ≤ Kgeom * (6 * κ ^ 3 * N ^ (2 * δ₀ * L) / rF) ∧
      (Kgeom ^ stripExpOf Kgeom κ N δ₀ L rF)⁻¹ * (6 * κ ^ 3 * N ^ (2 * δ₀ * L)) ≤ rF := by
  unfold stripExpOf
  have hNp : 1 ≤ N ^ (2 * δ₀ * L) := Real.one_le_rpow hN hδL
  have hκ3 : 1 ≤ κ ^ 3 := one_le_pow₀ hκ
  have hnum : 1 ≤ 6 * κ ^ 3 * N ^ (2 * δ₀ * L) := by nlinarith
  have hA : 1 ≤ 6 * κ ^ 3 * N ^ (2 * δ₀ * L) / rF := by
    rw [le_div_iff₀ hrF]; linarith
  obtain ⟨h1, h2⟩ := logCeil_spec hK hA
  refine ⟨h1, h2, ?_⟩
  have hpos : 0 < Kgeom ^ logCeil Kgeom (6 * κ ^ 3 * N ^ (2 * δ₀ * L) / rF) := by positivity
  rw [inv_mul_le_iff₀ hpos]
  have := (div_le_iff₀ hrF).mp h1
  linarith

/-- **The layer floor**: `((Kgeom^(3R+66))^qc)⁻¹ ≤ (Kgeom^w)⁻¹`. -/
theorem layer_floor {Kgeom : ℝ} (hK : 1 ≤ Kgeom) (w R : ℕ) :
    ((Kgeom ^ (3 * R + 66)) ^ layerQOf w R)⁻¹ ≤ (Kgeom ^ w)⁻¹ := by
  have h0 : 0 < Kgeom ^ w := by positivity
  rw [← pow_mul]
  exact inv_anti₀ h0 (pow_le_pow_right₀ hK (layerQ_spec w R).1)

/-- **The layer constant** pays `2 K^(3R+65)`. -/
theorem layer_const {K Kgeom : ℝ} (hK : 0 ≤ K) (hKK : K ≤ Kgeom) (h2 : 2 ≤ Kgeom) (R : ℕ) :
    2 * K ^ ((3 * R + 58) + 7) ≤ Kgeom ^ (3 * R + 66) := by
  have e : Kgeom ^ (3 * R + 66) = Kgeom * Kgeom ^ ((3 * R + 58) + 7) := by ring
  rw [e]
  have h := pow_le_pow_left₀ hK hKK ((3 * R + 58) + 7)
  have h0 : 0 ≤ K ^ ((3 * R + 58) + 7) := pow_nonneg hK _
  nlinarith

/-- **The deep margin** (`hdeep` of the census). -/
theorem deep_margin {K Kgeom κ N L δ₀ ub γ κ₁ ss sl : ℝ} {R J w : ℕ} {Tl Ts : ℕ}
    (hN : 1 < N) (hL : 0 < L) (hκ : 1 ≤ κ) (hκK : κ ≤ K) (hKK : K ≤ Kgeom)
    (hNK : N ^ (2 * δ₀ * L) ≤ Kgeom) (h24 : 24 ≤ Kgeom) (hγ : Kgeom ≤ N ^ (γ * L))
    (hδ : 0 ≤ δ₀) (hub : 0 ≤ ub)
    (hw : Kgeom ^ w ≤ Kgeom * (6 * κ ^ 3 * N ^ (2 * δ₀ * L) / N ^ (-(ub * L))))
    (hT : (2 : ℝ) ^ Tl / (2 : ℝ) ^ Ts ≤ N ^ (-((κ₁ * (ss - sl) - 2 * δ₀) * L)))
    (hmargin : γ * (deepPowerOf R J : ℝ) + ub + 2 * δ₀ ≤ κ₁ * (ss - sl)) :
    6 * K ^ R * ((1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) * ((2 : ℝ) ^ Tl / (2 : ℝ) ^ Ts)) ≤
      renewalCellMesh (Kgeom ^ (3 * R + 66)) J (layerQOf w R) := by
  have hNp : 0 < N := by linarith
  have hK1 : 1 ≤ Kgeom := by linarith
  have hK0 : 0 < Kgeom := by linarith
  have hκ0 : 0 < κ := by linarith
  have hNpow1 : 1 ≤ N ^ (2 * δ₀ * L) := Real.one_le_rpow hN.le (by positivity)
  have hκG : κ ≤ Kgeom := hκK.trans hKK
  -- the prefactor: `6 K^R (1 + κ³ N^(2δ₀L) + 2κ) ≤ Kgeom^(R+5)`
  have hpre : 6 * K ^ R * (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) ≤ Kgeom ^ (R + 5) := by
    have hκ3 : κ ^ 3 ≤ Kgeom ^ 3 := pow_le_pow_left₀ hκ0.le hκG 3
    have hκ31 : 1 ≤ κ ^ 3 := one_le_pow₀ hκ
    have h1 : 1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ ≤ 4 * (κ ^ 3 * N ^ (2 * δ₀ * L)) := by
      have : κ ≤ κ ^ 3 := le_self_pow₀ hκ (by norm_num)
      nlinarith
    have h2 : κ ^ 3 * N ^ (2 * δ₀ * L) ≤ Kgeom ^ 3 * Kgeom :=
      mul_le_mul hκ3 hNK (by positivity) (by positivity)
    have hKR : K ^ R ≤ Kgeom ^ R := pow_le_pow_left₀ (by linarith) hKK R
    have e : Kgeom ^ (R + 5) = Kgeom ^ R * (Kgeom ^ 3 * Kgeom * Kgeom) := by ring
    rw [e]
    have h3 : 6 * (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) ≤ Kgeom ^ 3 * Kgeom * Kgeom := by
      have h4 : 0 ≤ Kgeom ^ 3 * Kgeom := by positivity
      nlinarith
    calc 6 * K ^ R * (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ)
        = K ^ R * (6 * (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ)) := by ring
      _ ≤ Kgeom ^ R * (Kgeom ^ 3 * Kgeom * Kgeom) :=
          mul_le_mul hKR h3 (by positivity) (by positivity)
  -- the layer power: `(Kgeom^(3R+66))^(4J+qc+14) ≤ Kgeom^(P) N^(ub L)`
  have hA : 6 * κ ^ 3 * N ^ (2 * δ₀ * L) ≤ Kgeom ^ 5 := by
    have hκ3 : κ ^ 3 ≤ Kgeom ^ 3 := pow_le_pow_left₀ hκ0.le hκG 3
    have : 6 * κ ^ 3 * N ^ (2 * δ₀ * L) ≤ Kgeom * Kgeom ^ 3 * Kgeom :=
      mul_le_mul (mul_le_mul (by linarith) hκ3 (by positivity) (by positivity)) hNK
        (by positivity) (by positivity)
    calc 6 * κ ^ 3 * N ^ (2 * δ₀ * L) ≤ Kgeom * Kgeom ^ 3 * Kgeom := this
      _ = Kgeom ^ 5 := by ring
  have hw' : Kgeom ^ w ≤ Kgeom ^ 6 * N ^ (ub * L) := by
    have hdiv : 6 * κ ^ 3 * N ^ (2 * δ₀ * L) / N ^ (-(ub * L)) =
        6 * κ ^ 3 * N ^ (2 * δ₀ * L) * N ^ (ub * L) := by
      rw [Real.rpow_neg hNp.le, div_inv_eq_mul]
    rw [hdiv] at hw
    calc Kgeom ^ w ≤ Kgeom * (6 * κ ^ 3 * N ^ (2 * δ₀ * L) * N ^ (ub * L)) := hw
      _ ≤ Kgeom * (Kgeom ^ 5 * N ^ (ub * L)) := by gcongr
      _ = Kgeom ^ 6 * N ^ (ub * L) := by ring
  have hq := (layerQ_spec w R).2
  have hlayer : (Kgeom ^ (3 * R + 66)) ^ (4 * J + layerQOf w R + 14) ≤
      Kgeom ^ ((3 * R + 66) * (4 * J + 15) + 5) * N ^ (ub * L) := by
    rw [← pow_mul]
    have e1 : (3 * R + 66) * (4 * J + layerQOf w R + 14) =
        (3 * R + 66) * (4 * J + 14) + (3 * R + 66) * layerQOf w R := by ring
    rw [e1, pow_add]
    calc Kgeom ^ ((3 * R + 66) * (4 * J + 14)) * Kgeom ^ ((3 * R + 66) * layerQOf w R)
        ≤ Kgeom ^ ((3 * R + 66) * (4 * J + 14)) * Kgeom ^ (w + (3 * R + 65)) := by
          gcongr
      _ = Kgeom ^ ((3 * R + 66) * (4 * J + 14) + (3 * R + 65)) * Kgeom ^ w := by ring
      _ ≤ Kgeom ^ ((3 * R + 66) * (4 * J + 14) + (3 * R + 65)) * (Kgeom ^ 6 * N ^ (ub * L)) := by
          gcongr
      _ = Kgeom ^ ((3 * R + 66) * (4 * J + 15) + 5) * N ^ (ub * L) := by ring
  -- combine
  have hlpos : 0 < (Kgeom ^ (3 * R + 66)) ^ (4 * J + layerQOf w R + 14) := by positivity
  unfold renewalCellMesh
  rw [← one_div, le_div_iff₀ hlpos]
  have hdeep : Kgeom ^ deepPowerOf R J ≤ N ^ (γ * (deepPowerOf R J : ℝ) * L) := by
    calc Kgeom ^ deepPowerOf R J ≤ (N ^ (γ * L)) ^ deepPowerOf R J :=
          pow_le_pow_left₀ hK0.le hγ _
      _ = N ^ (γ * (deepPowerOf R J : ℝ) * L) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNp.le]; ring_nf
  have e2 : deepPowerOf R J = (R + 5) + ((3 * R + 66) * (4 * J + 15) + 5) := by
    unfold deepPowerOf; ring
  have hpre0 : 0 ≤ 6 * K ^ R * (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) := by
    have : 0 ≤ K := by linarith
    positivity
  calc 6 * K ^ R * ((1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ) * ((2 : ℝ) ^ Tl / (2 : ℝ) ^ Ts)) *
        (Kgeom ^ (3 * R + 66)) ^ (4 * J + layerQOf w R + 14)
      = (6 * K ^ R * (1 + κ ^ 3 * N ^ (2 * δ₀ * L) + 2 * κ)) * ((2 : ℝ) ^ Tl / (2 : ℝ) ^ Ts) *
        (Kgeom ^ (3 * R + 66)) ^ (4 * J + layerQOf w R + 14) := by ring
    _ ≤ Kgeom ^ (R + 5) * N ^ (-((κ₁ * (ss - sl) - 2 * δ₀) * L)) *
        (Kgeom ^ ((3 * R + 66) * (4 * J + 15) + 5) * N ^ (ub * L)) := by
        apply mul_le_mul (mul_le_mul hpre hT (by positivity) (by positivity)) hlayer
          (by positivity) (by positivity)
    _ = Kgeom ^ deepPowerOf R J * (N ^ (-((κ₁ * (ss - sl) - 2 * δ₀) * L)) * N ^ (ub * L)) := by
        rw [e2, pow_add]; ring
    _ ≤ N ^ (γ * (deepPowerOf R J : ℝ) * L) *
        (N ^ (-((κ₁ * (ss - sl) - 2 * δ₀) * L)) * N ^ (ub * L)) :=
        mul_le_mul_of_nonneg_right hdeep (by positivity)
    _ = N ^ ((γ * (deepPowerOf R J : ℝ) + ub + 2 * δ₀ - κ₁ * (ss - sl)) * L) := by
        rw [← Real.rpow_add hNp, ← Real.rpow_add hNp]; congr 1; ring
    _ ≤ N ^ (0 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hN.le
        have : γ * (deepPowerOf R J : ℝ) + ub + 2 * δ₀ - κ₁ * (ss - sl) ≤ 0 := by linarith
        nlinarith
    _ = 1 := Real.rpow_zero N

end Facts

end

end Submission.Obl.k4_isotropic_path_improvement.S294.Source
