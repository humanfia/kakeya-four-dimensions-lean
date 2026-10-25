/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.PolynomialLineField
import Submission.Lib.K4PolynomialNorming.AffineSwitchSimulation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FunProp

open Set MeasureTheory
open scoped Interval

namespace Submission.Lib.K4PolynomialNorming

/-- An assigned affine trajectory in normalized block time. -/
def affineLinePoint {L E : Type*} [AddCommGroup E] [Module ℝ E]
    (base velocity : L → E) (height speed : L → ℝ) (l : L) (t : ℝ) : E × ℝ :=
  (base l+t • velocity l,height l+t*speed l)

private theorem time_add_mem_unit_interval {t₀ t₁ s : ℝ}
    (h₀ : t₀ ∈ Icc (0:ℝ) 1) (h₁ : t₁ ∈ Icc (0:ℝ) 1)
    (hs : s ∈ uIcc (0:ℝ) (t₁-t₀)) : t₀+s ∈ Icc (0:ℝ) 1 := by
  rcases le_total t₀ t₁ with h | h
  · rw [uIcc_of_le (sub_nonneg.mpr h)] at hs
    constructor <;> linarith [h₀.1,h₁.2,hs.1,hs.2]
  · rw [uIcc_of_ge (sub_nonpos.mpr h)] at hs
    constructor <;> linarith [h₁.1,h₀.2,hs.1,hs.2]

/-- The actual assigned lines, shared-state errors and whole-block field
fits imply the physical endpoint simulation bound for all signed legs. -/
theorem assigned_affine_line_path_simulation {L E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (line : ℕ → L) (time : ℕ → ℝ)
    (base velocity coded : L → E) (height speed : L → ℝ)
    (F : E → E → ℝ) (hF : ∀ l, Continuous (F (coded l)))
    (ε η τ ζ M Lip R : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hLip : 0 ≤ Lip)
    (ht : ∀ k ≤ N, time k ∈ Icc (0:ℝ) 1)
    (hshared : ∀ k < N,
      ‖(affineLinePoint base velocity height speed (line (k+1)) (time k)).1-
        (affineLinePoint base velocity height speed (line k) (time k)).1‖ ≤ η)
    (hheight : ∀ k < N,
      |(affineLinePoint base velocity height speed (line (k+1)) (time k)).2-
        (affineLinePoint base velocity height speed (line k) (time k)).2| ≤ ζ)
    (hvelocity : ∀ k < N, ‖velocity (line (k+1))-coded (line (k+1))‖ ≤ τ)
    (hfit : ∀ k < N, ∀ t ∈ Icc (0:ℝ) 1,
      |speed (line (k+1))-F (velocity (line (k+1)))
        (base (line (k+1))+t • velocity (line (k+1)))| ≤ ε)
    (hconf : ∀ k < N, ∀ t ∈ Icc (0:ℝ) 1,
      ‖base (line (k+1))+t • velocity (line (k+1))‖ ≤ R)
    (hvel : ∀ k < N, ∀ x ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)),
      |F (velocity (line (k+1))) x-F (coded (line (k+1))) x| ≤
        M*‖velocity (line (k+1))-coded (line (k+1))‖)
    (hspace : ∀ k < N, ∀ x ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)),
      ∀ y ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)),
        |F (coded (line (k+1))) x-F (coded (line (k+1))) y| ≤ Lip*‖x-y‖) :
    let δ := fun k => time (k+1)-time k
    let v := fun k => coded (line (k+1))
    let c := fun k => (affineLinePoint base velocity height speed (line k) (time k)).1
    let z := fun k => (affineLinePoint base velocity height speed (line k) (time k)).2
    ‖pathBasePrefix (c 0) δ v N-c N‖ ≤ (N:ℝ)*(η+τ) ∧
    |(∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
      F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N| ≤
      (N:ℝ)*(ζ+ε+M*τ+Lip*(η+τ)+Lip*((N:ℝ)*(η+τ))) ∧
    ‖(pathBasePrefix (c 0) δ v N-c 0,
        ∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
          F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+
        (c 0,z 0)-(c N,z N)‖ ≤
      max ((N:ℝ)*(η+τ))
        ((N:ℝ)*(ζ+ε+M*τ+Lip*(η+τ)+Lip*((N:ℝ)*(η+τ)))) := by
  let δ := fun k => time (k+1)-time k
  let v := fun k => coded (line (k+1))
  let c := fun k => (affineLinePoint base velocity height speed (line k) (time k)).1
  let z := fun k => (affineLinePoint base velocity height speed (line k) (time k)).2
  let b := fun k => base (line (k+1))+time k • velocity (line (k+1))
  let u := fun k => velocity (line (k+1))
  let znew := fun k => height (line (k+1))+time k*speed (line (k+1))
  let rate := fun k => speed (line (k+1))
  let U := Metric.closedBall (0:E) (R+((N:ℝ)+1)*(η+τ))
  have hd : ∀ k < N, |δ k| ≤ 1 := by
    intro k hk
    obtain ⟨hkl,hku⟩ := ht k hk.le
    obtain ⟨hsl,hsu⟩ := ht (k+1) hk
    apply abs_le.mpr
    dsimp only [δ]
    constructor <;> linarith
  have hbe : ∀ k < N, c (k+1) = b k+δ k • u k := by
    intro k _
    dsimp [c,b,δ,u,affineLinePoint]
    module
  have hze : ∀ k < N, z (k+1) = znew k+δ k*rate k := by
    intro k _
    dsimp [z,znew,δ,rate,affineLinePoint]
    ring
  have hpoint (k : ℕ) (s : ℝ) :
      base (line (k+1))+(time k+s) • velocity (line (k+1)) = b k+s • u k := by
    dsimp only [b,u]
    module
  have hactual : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k), ‖b k+s • u k‖ ≤ R := by
    intro k hk s hs
    rw [← hpoint k s]
    exact hconf k hk _ (time_add_mem_unit_interval (ht k hk.le) (ht (k+1) hk) hs)
  have hregion := affine_switched_path_region N b c u v δ η τ R hη hτ hd hbe
    hshared hvelocity hactual
  have hsim := affine_switched_path_simulation N F b c u v z znew rate δ U ε η τ ζ M Lip
    (fun k => hF _) hε hη hτ hM hLip hd hbe hze hshared hvelocity hheight
    (fun k hk s hs => by
      rw [← hpoint k s]
      exact hfit k hk _ (time_add_mem_unit_interval (ht k hk.le) (ht (k+1) hk) hs))
    (fun k hk s hs => hvel k hk _ (hregion k hk s hs).1)
    hregion hspace
  have hbfinal : ‖pathBasePrefix (c 0) δ v N-c 0+c 0-c N‖ ≤ (N:ℝ)*(η+τ) := by
    rw [sub_add_cancel]
    simpa only [norm_sub_rev] using hsim.1 N le_rfl
  have hzfinal : ‖(∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N‖ ≤
        (N:ℝ)*(ζ+ε+M*τ+Lip*(η+τ)+Lip*((N:ℝ)*(η+τ))) := by
    rw [Real.norm_eq_abs, show (∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N =
      -(z N-z 0-∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        F (v k) (pathBasePrefix (c 0) δ v k+s • v k)) by ring,abs_neg]
    exact hsim.2
  refine ⟨?_,?_,?_⟩
  · simpa only [sub_add_cancel] using hbfinal
  · simpa only [Real.norm_eq_abs] using hzfinal
  · change max ‖pathBasePrefix (c 0) δ v N-c 0+c 0-c N‖
          ‖(∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
            F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N‖ ≤ _
    exact max_le_max hbfinal hzfinal

def quadraticHeight (a b c t : ℝ) : ℝ := a+t*b+t^2*c

def quadraticHeightSpeed (b c t : ℝ) : ℝ := b+2*t*c

/-- The actual signed increment of the native quadratic hidden coordinate. -/
theorem quadratic_height_signed_integral (a b c t₀ t₁ : ℝ) :
    (∫ s in (0:ℝ)..(t₁-t₀), quadraticHeightSpeed b c (t₀+s)) =
      quadraticHeight a b c t₁-quadraticHeight a b c t₀ := by
  have hd (s : ℝ) : HasDerivAt (fun x => quadraticHeight a b c (t₀+x))
      (quadraticHeightSpeed b c (t₀+s)) s := by
    have hs : HasDerivAt (fun x : ℝ => t₀+x) 1 s :=
      HasDerivAt.const_add t₀ (hasDerivAt_id s)
    change HasDerivAt (fun x => a+(t₀+x)*b+(t₀+x)^2*c) (b+2*(t₀+s)*c) s
    convert ((hasDerivAt_const s a).add (hs.mul_const b)).add ((hs.pow 2).mul_const c) using 1 <;>
      norm_num <;> ring
  have hc : Continuous (fun s => quadraticHeightSpeed b c (t₀+s)) := by
    unfold quadraticHeightSpeed
    fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hd s) (hc.intervalIntegrable 0 (t₁-t₀))
  have he : t₀+(t₁-t₀)=t₁ := by ring
  simpa only [he,add_zero] using h

/-- The native trajectory has an affine base and a quadratic hidden coordinate. -/
def quadraticLinePoint {L E : Type*} [AddCommGroup E] [Module ℝ E]
    (base velocity : L → E) (height₀ height₁ height₂ : L → ℝ) (l : L) (t : ℝ) : E × ℝ :=
  (base l+t • velocity l,quadraticHeight (height₀ l) (height₁ l) (height₂ l) t)

/-- Whole-block fits of the actual quadratic height derivatives imply
the separate base and hidden-coordinate simulation bounds. -/
theorem assigned_quadratic_line_path_simulation {L E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N : ℕ) (line : ℕ → L) (time : ℕ → ℝ)
    (base velocity coded : L → E) (height₀ height₁ height₂ : L → ℝ)
    (F : E → E → ℝ) (hF : ∀ l, Continuous (F (coded l)))
    (ε η τ ζ M Lip R : ℝ)
    (hε : 0 ≤ ε) (hη : 0 ≤ η) (hτ : 0 ≤ τ) (hM : 0 ≤ M) (hLip : 0 ≤ Lip)
    (ht : ∀ k ≤ N, time k ∈ Icc (0:ℝ) 1)
    (hshared : ∀ k < N,
      ‖(quadraticLinePoint base velocity height₀ height₁ height₂ (line (k+1)) (time k)).1-
        (quadraticLinePoint base velocity height₀ height₁ height₂ (line k) (time k)).1‖ ≤ η)
    (hheight : ∀ k < N,
      |(quadraticLinePoint base velocity height₀ height₁ height₂ (line (k+1)) (time k)).2-
        (quadraticLinePoint base velocity height₀ height₁ height₂ (line k) (time k)).2| ≤ ζ)
    (hvelocity : ∀ k < N, ‖velocity (line (k+1))-coded (line (k+1))‖ ≤ τ)
    (hfit : ∀ k < N, ∀ t ∈ Icc (0:ℝ) 1,
      |quadraticHeightSpeed (height₁ (line (k+1))) (height₂ (line (k+1))) t-F (velocity (line (k+1)))
        (base (line (k+1))+t • velocity (line (k+1)))| ≤ ε)
    (hconf : ∀ k < N, ∀ t ∈ Icc (0:ℝ) 1,
      ‖base (line (k+1))+t • velocity (line (k+1))‖ ≤ R)
    (hvel : ∀ k < N, ∀ x ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)),
      |F (velocity (line (k+1))) x-F (coded (line (k+1))) x| ≤
        M*‖velocity (line (k+1))-coded (line (k+1))‖)
    (hspace : ∀ k < N, ∀ x ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)),
      ∀ y ∈ Metric.closedBall 0 (R+((N:ℝ)+1)*(η+τ)),
        |F (coded (line (k+1))) x-F (coded (line (k+1))) y| ≤ Lip*‖x-y‖) :
    let δ := fun k => time (k+1)-time k
    let v := fun k => coded (line (k+1))
    let c := fun k => (quadraticLinePoint base velocity height₀ height₁ height₂ (line k) (time k)).1
    let z := fun k => (quadraticLinePoint base velocity height₀ height₁ height₂ (line k) (time k)).2
    ‖pathBasePrefix (c 0) δ v N-c N‖ ≤ (N:ℝ)*(η+τ) ∧
    |(∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
      F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N| ≤
      (N:ℝ)*(ζ+ε+M*τ+Lip*(η+τ)+Lip*((N:ℝ)*(η+τ))) ∧
    ‖(pathBasePrefix (c 0) δ v N-c 0,
        ∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
          F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+
        (c 0,z 0)-(c N,z N)‖ ≤
      max ((N:ℝ)*(η+τ))
        ((N:ℝ)*(ζ+ε+M*τ+Lip*(η+τ)+Lip*((N:ℝ)*(η+τ)))) := by
  let δ := fun k => time (k+1)-time k
  let v := fun k => coded (line (k+1))
  let c := fun k => (quadraticLinePoint base velocity height₀ height₁ height₂ (line k) (time k)).1
  let z := fun k => (quadraticLinePoint base velocity height₀ height₁ height₂ (line k) (time k)).2
  let b := fun k => base (line (k+1))+time k • velocity (line (k+1))
  let u := fun k => velocity (line (k+1))
  let znew := fun k => quadraticHeight (height₀ (line (k+1))) (height₁ (line (k+1)))
    (height₂ (line (k+1))) (time k)
  let g := fun k s => quadraticHeightSpeed (height₁ (line (k+1))) (height₂ (line (k+1))) (time k+s)
  let U := Metric.closedBall (0:E) (R+((N:ℝ)+1)*(η+τ))
  have hd : ∀ k < N, |δ k| ≤ 1 := by
    intro k hk
    obtain ⟨hkl,hku⟩ := ht k hk.le
    obtain ⟨hsl,hsu⟩ := ht (k+1) hk
    apply abs_le.mpr
    dsimp only [δ]
    constructor <;> linarith
  have hbe : ∀ k < N, c (k+1) = b k+δ k • u k := by
    intro k _
    dsimp [c,b,δ,u,quadraticLinePoint]
    module
  have hze : ∀ k < N, z (k+1)-znew k = ∫ s in (0:ℝ)..δ k, g k s := by
    intro k _
    dsimp only [z,znew,g,δ,quadraticLinePoint]
    exact (quadratic_height_signed_integral (height₀ (line (k+1))) (height₁ (line (k+1)))
      (height₂ (line (k+1))) (time k) (time (k+1))).symm
  have hpoint (k : ℕ) (s : ℝ) :
      base (line (k+1))+(time k+s) • velocity (line (k+1)) = b k+s • u k := by
    dsimp only [b,u]
    module
  have hactual : ∀ k < N, ∀ s ∈ uIcc (0:ℝ) (δ k), ‖b k+s • u k‖ ≤ R := by
    intro k hk s hs
    rw [← hpoint k s]
    exact hconf k hk _ (time_add_mem_unit_interval (ht k hk.le) (ht (k+1) hk) hs)
  have hregion := affine_switched_path_region N b c u v δ η τ R hη hτ hd hbe
    hshared hvelocity hactual
  have hsim := switched_path_simulation_of_fitted_height_integrals N F b c u v z znew δ g U
    ε η τ ζ M Lip (fun k => hF _) (fun k => by dsimp [g,quadraticHeightSpeed]; fun_prop)
    hε hη hτ hM hLip hd hbe hze hshared hvelocity hheight
    (fun k hk s hs => by
      rw [← hpoint k s]
      exact hfit k hk _ (time_add_mem_unit_interval (ht k hk.le) (ht (k+1) hk) hs))
    (fun k hk s hs => hvel k hk _ (hregion k hk s hs).1)
    hregion hspace
  have hbfinal : ‖pathBasePrefix (c 0) δ v N-c 0+c 0-c N‖ ≤ (N:ℝ)*(η+τ) := by
    rw [sub_add_cancel]
    simpa only [norm_sub_rev] using hsim.1 N le_rfl
  have hzfinal : ‖(∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N‖ ≤
        (N:ℝ)*(ζ+ε+M*τ+Lip*(η+τ)+Lip*((N:ℝ)*(η+τ))) := by
    rw [Real.norm_eq_abs, show (∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N =
      -(z N-z 0-∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
        F (v k) (pathBasePrefix (c 0) δ v k+s • v k)) by ring,abs_neg]
    exact hsim.2
  refine ⟨?_,?_,?_⟩
  · simpa only [sub_add_cancel] using hbfinal
  · simpa only [Real.norm_eq_abs] using hzfinal
  · change max ‖pathBasePrefix (c 0) δ v N-c 0+c 0-c N‖
          ‖(∑ k ∈ Finset.range N, ∫ s in (0:ℝ)..δ k,
            F (v k) (pathBasePrefix (c 0) δ v k+s • v k))+z 0-z N‖ ≤ _
    exact max_le_max hbfinal hzfinal


/-- The quadratic hidden coordinate has its explicit time Lipschitz
constant on the normalized unit interval. -/
theorem quadratic_height_time_difference_le (a b c t s : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) :
    |quadraticHeight a b c t-quadraticHeight a b c s| ≤
      |t-s| *(|b|+2*|c|) := by
  have hsum : |t+s| ≤ 2 := by
    rw [abs_of_nonneg (add_nonneg ht.1 hs.1)]
    linarith [ht.2,hs.2]
  have heq : quadraticHeight a b c t-quadraticHeight a b c s =
      (t-s)*(b+(t+s)*c) := by unfold quadraticHeight; ring
  rw [heq,abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  calc
    _ ≤ |b|+|(t+s)*c| := abs_add_le _ _
    _ = |b|+|t+s| *|c| := by rw [abs_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hsum (abs_nonneg _))

/-- Affine base motion of the native quadratic trajectory. -/
theorem quadratic_line_base_time_difference {L E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (base velocity : L → E) (height₀ height₁ height₂ : L → ℝ)
    (l : L) (t s : ℝ) :
    ‖(quadraticLinePoint base velocity height₀ height₁ height₂ l t).1-
        (quadraticLinePoint base velocity height₀ height₁ height₂ l s).1‖ =
      |t-s| *‖velocity l‖ := by
  change ‖(base l+t • velocity l)-(base l+s • velocity l)‖ = _
  rw [show (base l+t • velocity l)-(base l+s • velocity l) = (t-s) • velocity l by module,
    norm_smul,Real.norm_eq_abs]

/-- Same-cell point and time errors imply the shared-state errors needed
by the actual path simulation, after evaluating the new line at the old
time. Base and hidden-coordinate margins remain separate. -/
theorem quadratic_shared_state_error_of_point_time_error {L E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (base velocity : L → E) (height₀ height₁ height₂ : L → ℝ)
    (old new : L) (t s θ η₀ ζ₀ Mbase Mheight : ℝ)
    (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1)
    (htime : |t-s| ≤ θ) (hvelocity : ‖velocity new‖ ≤ Mbase)
    (hrate : |height₁ new|+2*|height₂ new| ≤ Mheight)
    (hbase : ‖(quadraticLinePoint base velocity height₀ height₁ height₂ new s).1-
      (quadraticLinePoint base velocity height₀ height₁ height₂ old t).1‖ ≤ η₀)
    (hheight : |(quadraticLinePoint base velocity height₀ height₁ height₂ new s).2-
      (quadraticLinePoint base velocity height₀ height₁ height₂ old t).2| ≤ ζ₀) :
    ‖(quadraticLinePoint base velocity height₀ height₁ height₂ new t).1-
        (quadraticLinePoint base velocity height₀ height₁ height₂ old t).1‖ ≤ η₀+θ*Mbase ∧
    |(quadraticLinePoint base velocity height₀ height₁ height₂ new t).2-
        (quadraticLinePoint base velocity height₀ height₁ height₂ old t).2| ≤ ζ₀+θ*Mheight := by
  have hθ : 0 ≤ θ := (abs_nonneg _).trans htime
  have hbs : ‖(quadraticLinePoint base velocity height₀ height₁ height₂ new t).1-
      (quadraticLinePoint base velocity height₀ height₁ height₂ new s).1‖ ≤ θ*Mbase := by
    rw [quadratic_line_base_time_difference]
    exact mul_le_mul htime hvelocity (norm_nonneg _) hθ
  have hhs : |(quadraticLinePoint base velocity height₀ height₁ height₂ new t).2-
      (quadraticLinePoint base velocity height₀ height₁ height₂ new s).2| ≤ θ*Mheight :=
    (quadratic_height_time_difference_le (height₀ new) (height₁ new) (height₂ new) t s ht hs).trans
      (mul_le_mul htime hrate (by positivity) hθ)
  constructor
  · calc
      _ ≤ ‖(quadraticLinePoint base velocity height₀ height₁ height₂ new t).1-
          (quadraticLinePoint base velocity height₀ height₁ height₂ new s).1‖+
        ‖(quadraticLinePoint base velocity height₀ height₁ height₂ new s).1-
          (quadraticLinePoint base velocity height₀ height₁ height₂ old t).1‖ := by
          simpa only [dist_eq_norm] using
            dist_triangle (quadraticLinePoint base velocity height₀ height₁ height₂ new t).1
              (quadraticLinePoint base velocity height₀ height₁ height₂ new s).1
              (quadraticLinePoint base velocity height₀ height₁ height₂ old t).1
      _ ≤ θ*Mbase+η₀ := add_le_add hbs hbase
      _ = _ := add_comm _ _
  · calc
      _ ≤ |(quadraticLinePoint base velocity height₀ height₁ height₂ new t).2-
          (quadraticLinePoint base velocity height₀ height₁ height₂ new s).2|+
        |(quadraticLinePoint base velocity height₀ height₁ height₂ new s).2-
          (quadraticLinePoint base velocity height₀ height₁ height₂ old t).2| := abs_sub_le _ _ _
      _ ≤ θ*Mheight+ζ₀ := add_le_add hhs hheight
      _ = _ := add_comm _ _

end Submission.Lib.K4PolynomialNorming
