import Submission.Obl.k4_fixed_budget_quadratic_recovery.PosteriorRecovery
import Submission.Obl.k4_fixed_budget_quadratic_recovery.QuadraticMatching
import Submission.Obl.k4_two_color_matching

/-!
# Separated posterior pairs are rare

Finitely many quadratic tests `F i` in the base coordinates `(t, y)`, with
`t ∈ [0, 1]` and `y ∈ [-Y, Y]`, are observed through component laws `comp i`
of an observation.  At a common observation two components agree to `τ`, and
every component has base marginal density at most `K`.  The accepted
two-colour matching theorem (o015), in the quadratic-sheet form of
`Submission.Lib.K4QuadSheetMatching`, bounds the unnormalized posterior-pair
mass of all pairs whose quadratics are separated somewhere on the base box.
The base box is rescaled onto the unit square, and the matching law is
normalized only by a fixed constant, never by its own mass.
-/

noncomputable section

namespace Submission.Obl.k4_fixed_budget_quadratic_recovery

open MeasureTheory Finset Set
open scoped ENNReal
open Submission.Lib.K4QuadSheetMatching

/-- Rescale the spatial base coordinate `[-Y, Y]` onto `[0, 1]`. -/
def rescaleBase (Y : ℝ) (z : ℝ × ℝ) : ℝ × ℝ := (z.1, (z.2 + Y) / (2 * Y))

/-- The coefficients of a quadratic in the rescaled base coordinates. -/
def rescaleCoeff (Y : ℝ) (c : Fin 6 → ℝ) : Fin 6 → ℝ :=
  ![c 0 - c 2 * Y + c 5 * Y ^ 2, c 1 - c 4 * Y, 2 * Y * c 2 - 4 * Y ^ 2 * c 5, c 3,
    2 * Y * c 4, 4 * Y ^ 2 * c 5]

theorem quadraticValue_rescaleCoeff (Y : ℝ) (c : Fin 6 → ℝ) (t w : ℝ) :
    quadraticValue (rescaleCoeff Y c) t w = quadraticValue c t (2 * Y * w - Y) := by
  simp [quadraticValue, rescaleCoeff]
  ring

theorem quadraticValue_rescaleBase {Y : ℝ} (hY : Y ≠ 0) (c : Fin 6 → ℝ) (z : ℝ × ℝ) :
    quadraticValue (rescaleCoeff Y c) (rescaleBase Y z).1 (rescaleBase Y z).2 =
      quadraticValue c z.1 z.2 := by
  rw [quadraticValue_rescaleCoeff]
  simp only [rescaleBase]
  congr 1
  field_simp
  ring

theorem measurable_rescaleBase (Y : ℝ) : Measurable (rescaleBase Y) := by
  unfold rescaleBase
  fun_prop

/-- The base box in the original coordinates. -/
def baseBox (Y : ℝ) : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-Y) Y

theorem rescaleBase_mem_unitSq {Y : ℝ} (hY : 0 < Y) {z : ℝ × ℝ} (hz : z ∈ baseBox Y) :
    rescaleBase Y z ∈ unitSq := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  refine ⟨⟨h1, h2⟩, ?_, ?_⟩
  · simp only [rescaleBase]
    apply div_nonneg <;> linarith
  · simp only [rescaleBase]
    rw [div_le_one (by positivity)]
    linarith

/-- A quadratic bounded coefficientwise by `H` is bounded by `6 H Y ^ 2` on the
rescaled unit square. -/
theorem rescaleCoeff_bound {Y H : ℝ} (hY : 1 ≤ Y) (hH : 0 ≤ H) {c : Fin 6 → ℝ}
    (hc : ∀ k, |c k| ≤ H) (w : ℝ × ℝ) (hw : w ∈ unitSq) :
    |quadraticValue (rescaleCoeff Y c) w.1 w.2| ≤ 6 * H * Y ^ 2 := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hw
  rw [quadraticValue_rescaleCoeff]
  apply quadraticValue_bound hH hY hc
  · rw [abs_le]
    constructor <;> linarith
  · rw [abs_le]
    constructor <;> nlinarith

/-- The rescaling multiplies Lebesgue measure of preimages by `2 Y`. -/
theorem volume_rescaleBase_preimage {Y : ℝ} (hY : 0 < Y) {B : Set (ℝ × ℝ)}
    (hB : MeasurableSet B) :
    volume (rescaleBase Y ⁻¹' B) = ENNReal.ofReal (2 * Y) * volume B := by
  have hpre : MeasurableSet (rescaleBase Y ⁻¹' B) := measurable_rescaleBase Y hB
  rw [Measure.volume_eq_prod, Measure.prod_apply hpre, Measure.prod_apply hB,
    ← lintegral_const_mul _ (measurable_measure_prodMk_left hB)]
  apply lintegral_congr
  intro t
  have hfib : Prod.mk t ⁻¹' (rescaleBase Y ⁻¹' B) =
      (fun y : ℝ => y + Y) ⁻¹' ((fun y : ℝ => (2 * Y)⁻¹ * y) ⁻¹' (Prod.mk t ⁻¹' B)) := by
    ext y
    simp only [Set.mem_preimage, rescaleBase]
    rw [div_eq_inv_mul]
  rw [hfib, measure_preimage_add_right, Real.volume_preimage_mul_left (by positivity),
    inv_inv, abs_of_pos (by positivity)]

section Pairs

variable {Obs : Type*} [MeasurableSpace Obs]

/-- Two tests are separated at level `r` somewhere on the base box. -/
def SeparatedPair {n : ℕ} (F : Fin n → Fin 6 → ℝ) (Y r : ℝ) (ι : Fin n × Fin n) : Prop :=
  ∃ w ∈ baseBox Y, r ≤ |quadraticValue (F ι.1) w.1 w.2 - quadraticValue (F ι.2) w.1 w.2|

/-- The unnormalized posterior law of one ordered pair of components. -/
def componentPairLaw {n : ℕ} (comp : Fin n → Measure Obs) (ι : Fin n × Fin n) : Measure Obs :=
  (∑ k, comp k).withDensity
    (fun o => componentPosterior comp o ι.1 * componentPosterior comp o ι.2)

theorem componentPosterior_le_one {n : ℕ} (comp : Fin n → Measure Obs)
    [∀ i, IsFiniteMeasure (comp i)] (j : Fin n) :
    ∀ᵐ o ∂(∑ k, comp k), componentPosterior comp o j ≤ 1 := by
  filter_upwards [componentPosterior_mass comp] with o ho
  rw [← ho]
  exact Finset.single_le_sum (f := fun b => componentPosterior comp o b)
    (fun _ _ => zero_le) (Finset.mem_univ j)

theorem componentPairLaw_le_fst {n : ℕ} (comp : Fin n → Measure Obs)
    [∀ i, IsFiniteMeasure (comp i)] (ι : Fin n × Fin n) :
    componentPairLaw comp ι ≤ comp ι.1 := by
  calc
    componentPairLaw comp ι ≤ (∑ k, comp k).withDensity
        (fun o => componentPosterior comp o ι.1) := by
      apply withDensity_mono
      filter_upwards [componentPosterior_le_one comp ι.2] with o ho
      calc
        componentPosterior comp o ι.1 * componentPosterior comp o ι.2 ≤
            componentPosterior comp o ι.1 * 1 := mul_le_mul_right ho _
        _ = _ := mul_one _
    _ = comp ι.1 := componentPosterior_density comp ι.1

theorem componentPairLaw_le_snd {n : ℕ} (comp : Fin n → Measure Obs)
    [∀ i, IsFiniteMeasure (comp i)] (ι : Fin n × Fin n) :
    componentPairLaw comp ι ≤ comp ι.2 := by
  calc
    componentPairLaw comp ι ≤ (∑ k, comp k).withDensity
        (fun o => componentPosterior comp o ι.2) := by
      apply withDensity_mono
      filter_upwards [componentPosterior_le_one comp ι.1] with o ho
      calc
        componentPosterior comp o ι.1 * componentPosterior comp o ι.2 ≤
            1 * componentPosterior comp o ι.2 := mul_le_mul_left ho _
        _ = _ := one_mul _
    _ = comp ι.2 := componentPosterior_density comp ι.2

theorem sum_componentPairLaw_fst {n : ℕ} (comp : Fin n → Measure Obs)
    [∀ i, IsFiniteMeasure (comp i)] (i : Fin n) (S : Set Obs) :
    ∑ j, componentPairLaw comp (i, j) S = comp i S := by
  have hπ := componentPosterior_measurable comp
  rw [← Measure.finsetSum_apply]
  unfold componentPairLaw
  rw [← withDensity_finite_sum _ (fun j o => componentPosterior comp o i *
    componentPosterior comp o j) (fun j => (hπ i).mul (hπ j))]
  rw [← componentPosterior_density comp i]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [componentPosterior_mass comp] with o ho
  rw [← Finset.mul_sum, ho, mul_one]

theorem sum_componentPairLaw_snd {n : ℕ} (comp : Fin n → Measure Obs)
    [∀ i, IsFiniteMeasure (comp i)] (j : Fin n) (S : Set Obs) :
    ∑ i, componentPairLaw comp (i, j) S = comp j S := by
  have hπ := componentPosterior_measurable comp
  rw [← Measure.finsetSum_apply]
  unfold componentPairLaw
  rw [← withDensity_finite_sum _ (fun i o => componentPosterior comp o i *
    componentPosterior comp o j) (fun i => (hπ i).mul (hπ j))]
  rw [← componentPosterior_density comp j]
  congr 1
  apply withDensity_congr_ae
  filter_upwards [componentPosterior_mass comp] with o ho
  rw [← Finset.sum_mul, ho, one_mul]

open scoped Classical in
/-- **Separated posterior pairs are rare.**  The accepted two-colour matching
theorem bounds the unnormalized posterior mass of pairs of tests separated at
level `R ^ (-ε)` on the base box. -/
theorem separated_component_pair_mass {d₀ : ℝ} (hd0 : 0 ≤ d₀) (hd1 : d₀ < 1) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ R₀ : ℝ, 2 ≤ R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
    ∀ (n : ℕ) (comp : Fin n → Measure Obs), (∀ i, IsFiniteMeasure (comp i)) →
    ∀ (base : Obs → ℝ × ℝ) (signal : Obs → ℝ) (F : Fin n → Fin 6 → ℝ) (Y H τ K : ℝ),
    Measurable base → Measurable signal → 1 ≤ Y → 0 < K → 0 ≤ H →
    (n : ℝ) ≤ R ^ (d₀ + ε) → (∀ i k, |F i k| ≤ H) → 6 * H * Y ^ 2 ≤ R ^ ε →
    2 * τ ≤ R ^ (-1 + ε) →
    (∀ i, ∀ᵐ o ∂comp i, base o ∈ baseBox Y ∧
      |signal o - quadraticValue (F i) (base o).1 (base o).2| ≤ τ) →
    (∀ i E, MeasurableSet E → comp i (base ⁻¹' E) ≤ ENNReal.ofReal K * volume E) →
    (∑ ι : Fin n × Fin n, if SeparatedPair F Y (R ^ (-ε)) ι then
        componentPairLaw comp ι univ else 0) ≤
      ENNReal.ofReal (n * K * (2 * Y) * R ^ (-2 * ε)) := by
  obtain ⟨ε, hε, R₀, hR₀, hmatch⟩ :=
    quadratic_separated_pair_mass Submission.k4_two_color_matching hd0 hd1
  refine ⟨ε, hε, R₀, hR₀, ?_⟩
  intro R hR n comp hcomp base signal F Y H τ K hbase hsignal hY hK hH hnR hF hFY hτ
    hagree hmarg
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hY0 : 0 < Y := by linarith
  have hR1 : 1 ≤ R := by linarith
  have hR0 : 0 < R := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  set κ : ℝ := R ^ ε / (n * K * (2 * Y)) with hκ
  have hκpos : 0 < κ := by positivity
  set g : Obs → ℝ × ℝ := rescaleBase Y ∘ base with hgdef
  have hg : Measurable g := (measurable_rescaleBase Y).comp hbase
  set ρm : Fin n × Fin n → Measure (ℝ × ℝ) :=
    fun ι => ENNReal.ofReal κ • (componentPairLaw comp ι).map g with hρm
  have hfinpair (ι : Fin n × Fin n) : IsFiniteMeasure (componentPairLaw comp ι) :=
    isFiniteMeasure_of_le (comp ι.1) (componentPairLaw_le_fst comp ι)
  have hfin (ι : Fin n × Fin n) : IsFiniteMeasure (ρm ι) := by
    refine ⟨?_⟩
    simp only [hρm, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)
  have hρm_apply (ι : Fin n × Fin n) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
      ρm ι B = ENNReal.ofReal κ * componentPairLaw comp ι (g ⁻¹' B) := by
    simp only [hρm, Measure.smul_apply, smul_eq_mul, Measure.map_apply hg hB]
  -- the component marginal in rescaled coordinates
  have hcompB (i : Fin n) {B : Set (ℝ × ℝ)} (hB : MeasurableSet B) :
      ENNReal.ofReal κ * comp i (g ⁻¹' B) ≤
        ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) * volume B := by
    have hpre : g ⁻¹' B = base ⁻¹' (rescaleBase Y ⁻¹' B) := rfl
    rw [hpre]
    calc
      ENNReal.ofReal κ * comp i (base ⁻¹' (rescaleBase Y ⁻¹' B)) ≤
          ENNReal.ofReal κ * (ENNReal.ofReal K * volume (rescaleBase Y ⁻¹' B)) :=
        mul_le_mul_right (hmarg i _ (measurable_rescaleBase Y hB)) _
      _ = ENNReal.ofReal (κ * K * (2 * Y)) * volume B := by
        rw [volume_rescaleBase_preimage hY0 hB,
          ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ κ * K),
          ENNReal.ofReal_mul hκpos.le]
        ring
      _ = ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) * volume B := by
        congr 2
        rw [hκ]
        field_simp
  have hmarg₁ : ∀ i (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ j, ρm (i, j) B ≤ ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) * volume B := by
    intro i B hB
    simp_rw [hρm_apply _ hB]
    rw [← Finset.mul_sum, sum_componentPairLaw_fst comp i]
    exact hcompB i hB
  have hmarg₂ : ∀ j (B : Set (ℝ × ℝ)), MeasurableSet B →
      ∑ i, ρm (i, j) B ≤ ENNReal.ofReal (R ^ ε * (1 / (n : ℝ))) * volume B := by
    intro j B hB
    simp_rw [hρm_apply _ hB]
    rw [← Finset.mul_sum, sum_componentPairLaw_snd comp j]
    exact hcompB j hB
  have hnear : ∀ ι, ∀ᵐ z ∂ρm ι, z ∈ unitSq ∧
      |quadraticValue (rescaleCoeff Y (F ι.1)) z.1 z.2 -
        quadraticValue (rescaleCoeff Y (F ι.2)) z.1 z.2| ≤ R ^ (-1 + ε) := by
    intro ι
    apply Measure.ae_smul_measure
    have hset : MeasurableSet {z : ℝ × ℝ | z ∈ unitSq ∧
        |quadraticValue (rescaleCoeff Y (F ι.1)) z.1 z.2 -
          quadraticValue (rescaleCoeff Y (F ι.2)) z.1 z.2| ≤ R ^ (-1 + ε)} := by
      have hU : MeasurableSet unitSq := measurableSet_Icc.prod measurableSet_Icc
      refine hU.inter ?_
      have hq (c : Fin 6 → ℝ) : Measurable (fun z : ℝ × ℝ => quadraticValue c z.1 z.2) := by
        unfold quadraticValue
        fun_prop
      exact measurableSet_le (((hq _).sub (hq _)).abs) measurable_const
    rw [ae_map_iff hg.aemeasurable hset]
    filter_upwards [ae_mono (componentPairLaw_le_fst comp ι) (hagree ι.1),
      ae_mono (componentPairLaw_le_snd comp ι) (hagree ι.2)] with o h₁ h₂
    refine ⟨rescaleBase_mem_unitSq hY0 h₁.1, ?_⟩
    simp only [hgdef, Function.comp_apply]
    rw [quadraticValue_rescaleBase hY0.ne', quadraticValue_rescaleBase hY0.ne']
    calc
      _ ≤ |signal o - quadraticValue (F ι.1) (base o).1 (base o).2| +
          |signal o - quadraticValue (F ι.2) (base o).1 (base o).2| := by
        rw [abs_sub_comm (signal o)]
        exact abs_sub_le _ _ _
      _ ≤ τ + τ := add_le_add h₁.2 h₂.2
      _ ≤ R ^ (-1 + ε) := by linarith
  have hnear' : ∀ ι, ∀ᵐ z ∂ρm ι, z ∈ unitSq ∧
      |quadraticValue (rescaleCoeff Y (F ι.1)) z.1 z.2 -
        quadraticValue (rescaleCoeff Y (F ι.2)) z.1 z.2| ≤ R ^ (-1 + ε) := hnear
  have key := hmatch R hR n n (fun i => rescaleCoeff Y (F i)) (fun i => rescaleCoeff Y (F i))
    (fun _ => 1 / (n : ℝ)) (fun _ => 1 / (n : ℝ)) ρm hfin hnR hnR
    (fun i w hw => (rescaleCoeff_bound hY hH (hF i) w hw).trans hFY)
    (fun i w hw => (rescaleCoeff_bound hY hH (hF i) w hw).trans hFY)
    (fun _ => by positivity) (fun _ => by positivity)
    (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    (by simp [Finset.sum_const, Finset.card_univ]; field_simp)
    hmarg₁ hmarg₂ hnear'
  -- compare the two sums termwise
  have hterm (ι : Fin n × Fin n) :
      ENNReal.ofReal κ * (if SeparatedPair F Y (R ^ (-ε)) ι then
          componentPairLaw comp ι univ else 0) ≤
        (if (∃ w ∈ unitSq, R ^ (-ε) ≤
          |quadraticValue (rescaleCoeff Y (F ι.1)) w.1 w.2 -
            quadraticValue (rescaleCoeff Y (F ι.2)) w.1 w.2|) then ρm ι univ else 0) := by
    by_cases hsep : SeparatedPair F Y (R ^ (-ε)) ι
    · obtain ⟨w, hw, hwv⟩ := hsep
      have hsep' : ∃ w ∈ unitSq, R ^ (-ε) ≤
          |quadraticValue (rescaleCoeff Y (F ι.1)) w.1 w.2 -
            quadraticValue (rescaleCoeff Y (F ι.2)) w.1 w.2| := by
        refine ⟨rescaleBase Y w, rescaleBase_mem_unitSq hY0 hw, ?_⟩
        rw [quadraticValue_rescaleBase hY0.ne', quadraticValue_rescaleBase hY0.ne']
        exact hwv
      rw [if_pos ⟨w, hw, hwv⟩, if_pos hsep', hρm_apply ι MeasurableSet.univ, Set.preimage_univ]
    · rw [if_neg hsep, mul_zero]
      exact zero_le
  have hsum : ENNReal.ofReal κ * (∑ ι : Fin n × Fin n, if SeparatedPair F Y (R ^ (-ε)) ι then
      componentPairLaw comp ι univ else 0) < ENNReal.ofReal (R ^ (-ε)) := by
    rw [Finset.mul_sum]
    exact lt_of_le_of_lt (Finset.sum_le_sum (fun ι _ => hterm ι)) key
  by_contra hbig
  push_neg at hbig
  have hprod : ENNReal.ofReal κ * ENNReal.ofReal (n * K * (2 * Y) * R ^ (-2 * ε)) =
      ENNReal.ofReal (R ^ (-ε)) := by
    rw [← ENNReal.ofReal_mul hκpos.le]
    congr 1
    rw [hκ]
    have h2 : R ^ ε * R ^ (-2 * ε) = R ^ (-ε) := by
      rw [← Real.rpow_add hR0]
      congr 1
      ring
    have hD : (n : ℝ) * K * (2 * Y) ≠ 0 := by positivity
    calc R ^ ε / (↑n * K * (2 * Y)) * (↑n * K * (2 * Y) * R ^ (-2 * ε))
        = R ^ ε * R ^ (-2 * ε) := by field_simp
      _ = R ^ (-ε) := h2
  have := mul_le_mul_right hbig.le (ENNReal.ofReal κ)
  rw [hprod] at this
  exact absurd (this.trans_lt hsum) (lt_irrefl _)

end Pairs

end Submission.Obl.k4_fixed_budget_quadratic_recovery
