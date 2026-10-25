import Submission.Obl.k4_physical_parent_potential_candidates.FubiniImplicitRestoration

namespace Submission.Obl.k4_physical_parent_potential_candidates

open Set FubiniJets FubiniHessian FubiniProductJets

noncomputable section

namespace FubiniZoom

def map (c : FubiniBase) (r : ℝ) (x : FubiniBase) : FubiniBase := c+r • x

def pull (f : FubiniBase → ℝ) (c : FubiniBase) (r : ℝ) (x : FubiniBase) : ℝ := f (map c r x)

theorem continuous_map (c : FubiniBase) (r : ℝ) : Continuous (map c r) := by unfold map; fun_prop

theorem contDiffOn_pull {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U W : Set FubiniBase}
    (hf : ContDiffOn ℝ N f U) (c : FubiniBase) (r : ℝ) (hmap : MapsTo (map c r) W U) :
    ContDiffOn ℝ N (pull f c r) W := by
  exact hf.comp (by unfold map; fun_prop) hmap

/-- Exact derivative scaling for a local affine base zoom. -/
theorem iteratedFDeriv_pull
    {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {n : ℕ} (hn : (n:WithTop ℕ∞) ≤ N)
    (c : FubiniBase) (r : ℝ) (x : FubiniBase) (hx : map c r x ∈ U) :
    iteratedFDeriv ℝ n (pull f c r) x = r^n • iteratedFDeriv ℝ n f (map c r x) := by
  let L : FubiniBase →L[ℝ] FubiniBase := r • ContinuousLinearMap.id ℝ FubiniBase
  let V := (fun z : FubiniBase => c+z) ⁻¹' U
  have hV : IsOpen V := hU.preimage (by fun_prop)
  have hs : ContDiffOn ℝ N (fun z : FubiniBase => f (c+z)) V :=
    hf.comp (by fun_prop) (fun _ hz => hz)
  have hVL : IsOpen (L ⁻¹' V) := hV.preimage L.continuous
  have hxV : L x ∈ V := hx
  have hh := L.iteratedFDerivWithin_comp_right hs hV.uniqueDiffOn hVL.uniqueDiffOn hxV hn
  rw [iteratedFDerivWithin_of_isOpen n hVL hxV,
    iteratedFDerivWithin_of_isOpen n hV hxV, iteratedFDeriv_comp_add_left] at hh
  ext m
  have he := congrArg (fun T => T m) hh
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, L,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    ContinuousMultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at he
  exact he

theorem jet_pull {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {n : ℕ} (hn : (n:WithTop ℕ∞) ≤ N)
    (c : FubiniBase) (r : ℝ) (x : FubiniBase) (hx : map c r x ∈ U) (α : Fin n → Fin 3) :
    jet (pull f c r) n α x = r^n*jet f n α (map c r x) := by
  unfold jet
  rw [iteratedFDeriv_pull hU hf hn c r x hx]
  rfl

theorem norm_pull_bound {f : FubiniBase → ℝ} {N : WithTop ℕ∞} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ N f U) {n : ℕ} (hn : (n:WithTop ℕ∞) ≤ N)
    (c : FubiniBase) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : FubiniBase)
    (hx : map c r x ∈ U) {K : ℝ} (hb : ‖iteratedFDeriv ℝ n f (map c r x)‖ ≤ K) :
    ‖iteratedFDeriv ℝ n (pull f c r) x‖ ≤ K := by
  rw [iteratedFDeriv_pull hU hf hn c r x hx, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hr n)]
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hr hr1)).trans hb

theorem hessian_pull {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (c : FubiniBase) (r : ℝ) (x : FubiniBase)
    (hx : map c r x ∈ U) : hessian (pull f c r) x = r^2 • hessian f (map c r x) := by
  ext i j
  exact jet_pull hU hf (by norm_num) c r x hx ![i,j]

theorem cubic_pull {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (c : FubiniBase) (r : ℝ) (x : FubiniBase)
    (hx : map c r x ∈ U) (i j k : Fin 3) :
    cubic (pull f c r) x i j k = r^3*cubic f (map c r x) i j k :=
  jet_pull hU hf (by norm_num) c r x hx ![i,j,k]

theorem det_hessian_pull {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (c : FubiniBase) (r : ℝ) (x : FubiniBase)
    (hx : map c r x ∈ U) :
    (hessian (pull f c r) x).det = r^6*(hessian f (map c r x)).det := by
  rw [hessian_pull hU hf c r x hx, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

/-- Clearing the canonical tensor before zooming avoids differentiating
any inverse Hessian or logarithmic connection in the change of coordinates. -/
theorem cleared_pull {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (c : FubiniBase) (r : ℝ) (x : FubiniBase)
    (hx : map c r x ∈ U) (i j k : Fin 3) :
    clearedCubicError (pull f c r) x i j k = r^9*clearedCubicError f (map c r x) i j k := by
  have hc : cubic (pull f c r) x = fun i j k => r^3*cubic f (map c r x) i j k := by
    funext i j k
    exact cubic_pull hU hf c r x hx i j k
  rw [clearedCubicError, hessian_pull hU hf c r x hx, hc,
    ConicTensor.cleared_smul, ConicTensor.cleared_const_mul]
  dsimp only [clearedCubicError]
  ring

/-- The cleared numerator is smooth before any determinant regularity
restriction; it is a polynomial in the graph's second and third jets. -/
theorem cleared_smooth {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (i j k : Fin 3) :
    ContDiffOn ℝ 3 (fun x => clearedCubicError f x i j k) U := by
  have hH (i j : Fin 3) : ContDiffOn ℝ 3 (fun x => hessian f x i j) U :=
    contDiffOn_jet hU hf (by norm_num) ![i,j]
  have hC (i j k : Fin 3) : ContDiffOn ℝ 3 (fun x => cubic f x i j k) U :=
    contDiffOn_jet hU hf (by norm_num) ![i,j,k]
  have hdet : ContDiffOn ℝ 3 (fun x => (hessian f x).det) U := by
    simp only [Matrix.det_fin_three]
    fun_prop
  have hadj (a b : Fin 3) : ContDiffOn ℝ 3 (fun x => (hessian f x).adjugate a b) U := by
    simp only [Matrix.adjugate_fin_three]
    fin_cases a <;> fin_cases b <;> simp <;> fun_prop
  have hn (l : Fin 3) : ContDiffOn ℝ 3 (fun x => ∑ a : Fin 3, ∑ b : Fin 3,
      (hessian f x).adjugate a b*cubic f x l a b) U :=
    ContDiffOn.sum (fun a _ => ContDiffOn.sum (fun b _ => (hadj a b).mul (hC l a b)))
  exact ((contDiffOn_const.mul hdet).mul (hC i j k)).sub
    ((((hn i).mul (hH j k)).add ((hn j).mul (hH i k))).add ((hn k).mul (hH i j)))

/-- Coordinate jets of the cleared numerator acquire exactly r^(9+n). -/
theorem jet_cleared_pull {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (c : FubiniBase) (r : ℝ) (x : FubiniBase)
    (hx : map c r x ∈ U) {n : ℕ} (hn : n ≤ 2) (α : Fin n → Fin 3) (i j k : Fin 3) :
    jet (fun y => clearedCubicError (pull f c r) y i j k) n α x =
      r^(9+n)*jet (fun y => clearedCubicError f y i j k) n α (map c r x) := by
  let W := map c r ⁻¹' U
  have hW : IsOpen W := hU.preimage (continuous_map c r)
  have heq : EqOn (fun y => clearedCubicError (pull f c r) y i j k)
      (fun y => r^9*pull (fun z => clearedCubicError f z i j k) c r y) W := by
    intro y hy
    exact cleared_pull hU hf c r y hy i j k
  have hn3 : (n:WithTop ℕ∞) ≤ 3 := by exact_mod_cast hn.trans (by decide : 2 ≤ 3)
  have hs := cleared_smooth hU hf i j k
  rw [jet_eq_of_eqOn hW heq hx,
    jet_const_mul hW (contDiffOn_pull hs c r (fun _ hy => hy)) hx (r^9) n hn3,
    jet_pull hU hs hn3 c r x hx, pow_add]
  ring

/-- A contraction of the base scale never increases the C² error of the
cleared numerator. -/
theorem cleared_pull_C2_bound {f : FubiniBase → ℝ} {U : Set FubiniBase}
    (hU : IsOpen U) (hf : ContDiffOn ℝ 6 f U) (c : FubiniBase) {r : ℝ}
    (hr : 0 ≤ r) (hr1 : r ≤ 1) (x : FubiniBase) (hx : map c r x ∈ U)
    {ε : ℝ} (hb : ∀ i j k, C2Bound (fun y => clearedCubicError f y i j k) ε (map c r x)) :
    ∀ i j k, C2Bound (fun y => clearedCubicError (pull f c r) y i j k) ε x := by
  have hp (n : ℕ) {v : ℝ} (hv : |v| ≤ ε) : |r^n*v| ≤ ε := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hr n)]
    exact (mul_le_of_le_one_left (abs_nonneg _) (pow_le_one₀ hr hr1)).trans hv
  intro i j k
  refine ⟨?_, ?_, ?_⟩
  · rw [cleared_pull hU hf c r x hx]
    exact hp 9 (hb i j k).value
  · intro p
    rw [jet_cleared_pull hU hf c r x hx (by decide : 1 ≤ 2)]
    exact hp 10 ((hb i j k).first p)
  · intro p l
    rw [jet_cleared_pull hU hf c r x hx (by decide : 2 ≤ 2)]
    exact hp 11 ((hb i j k).second p l)

end FubiniZoom

end

end Submission.Obl.k4_physical_parent_potential_candidates
