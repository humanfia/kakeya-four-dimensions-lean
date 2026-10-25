import Submission.Obl.k4_physical_parent_potential_candidates.PhysicalSource

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

namespace SourceNormalization

/-- Padding the analytic error above the actual incidence error keeps every
retained source event inside the eventual quadratic tube. -/
def errorPadding (A : ℝ) (C : ℕ) (a w : ℝ) : ℝ := A^(C+30)*(a*w)

def paddedError (A : ℝ) (C : ℕ) (a w epsc Mz hdelta : ℝ) : ℝ :=
  epsc+errorPadding A C a w+Mz*hdelta

structure SourceErrorBounds (A K a w zeta lam eps fit epsc Mz : ℝ) (C : ℕ) : Prop where
  zeta_le_width : zeta ≤ w
  mesh_nonneg : 0 ≤ lam*eps
  mesh_half : lam*eps ≤ 1/2
  mesh_accuracy : lam*eps*A^C ≤ 1
  mesh_covers_state : 3*lam*eps/(8*K) ≤ lam*eps
  error_pos : 0 < paddedError A C a w epsc Mz (lam*eps)
  padding_le_error : errorPadding A C a w ≤ paddedError A C a w epsc Mz (lam*eps)
  width_le_error : a*w ≤ paddedError A C a w epsc Mz (lam*eps)
  error_upper : paddedError A C a w epsc Mz (lam*eps) ≤ A^(C+31)*(a*w)
  error_accuracy : paddedError A C a w epsc Mz (lam*eps)*A^C ≤ 1
  fit_input : fit*(2*K)^19 ≤ A*errorPadding A C a w
  fit_in_tube : A^C*(fit*(2*K)^19) ≤ paddedError A C a w epsc Mz (lam*eps)

/-- The stronger packet margin pays all normalized error conditions using
only the original physical clock and its original fine mesh. -/
theorem source_error_bounds {A K h a zeta eps w lam fit epsc Mz : ℝ} (C : ℕ)
    (hA : 2 ≤ A) (hK : 2 ≤ K) (hKA : 2*K ≤ A)
    (hh : 0 < h) (ha : 0 < a) (hzeta : 0 ≤ zeta) (heps : 0 ≤ eps)
    (hw : 0 < w) (hw2 : 2*w ≤ 1) (hlam : 1 ≤ lam) (hlamA : lam ≤ A)
    (haK : a ≤ K*h) (hhzeta : h ≤ zeta) (hepszeta : eps ≤ zeta)
    (hclock : h*eps ≤ a*zeta) (hfit : fit ≤ A*(a*w))
    (hepsc : 0 ≤ epsc) (hepscA : epsc ≤ A*a*zeta)
    (hMz : 0 ≤ Mz) (hMzA : Mz ≤ A*h)
    (hmargin : A^(2*C+40)*zeta ≤ w) :
    SourceErrorBounds A K a w zeta lam eps fit epsc Mz C := by
  have hA0 : 0 < A := by linarith
  have hA1 : 1 ≤ A := by linarith
  have hK0 : 0 < K := by linarith
  have hKle : K ≤ A := by linarith
  have hw1 : w ≤ 1 := by linarith
  have haw : 0 < a*w := mul_pos ha hw
  have hLam0 : 0 ≤ lam := by linarith
  have hsmall (n : ℕ) (hn : n ≤ 2*C+40) : A^n*zeta ≤ w :=
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 hn) hzeta).trans hmargin
  have hzetaW : zeta ≤ w := by simpa using hsmall 0 (by omega)
  have hmesh0 : 0 ≤ lam*eps := mul_nonneg hLam0 heps
  have hmesh (n : ℕ) : lam*eps*A^n ≤ A^(n+1)*zeta := by
    calc
      _ ≤ A*zeta*A^n := by gcongr
      _ = _ := by rw [pow_succ]; ring
  have hmeshW : lam*eps ≤ w := by
    have hm : lam*eps ≤ A*zeta := by simpa using hmesh 0
    exact hm.trans (by simpa only [pow_one] using hsmall 1 (by omega))
  have hterm : Mz*(lam*eps) ≤ A^2*a*zeta := by
    calc
      _ ≤ (A*h)*(A*eps) := by gcongr
      _ = A^2*(h*eps) := by ring
      _ ≤ A^2*(a*zeta) := by gcongr
      _ = _ := by ring
  have hA2 : A ≤ A^2 := by simpa using pow_le_pow_right₀ hA1 (by decide : 1 ≤ 2)
  have herr : paddedError A C a w epsc Mz (lam*eps) ≤ A^(C+31)*(a*w) := by
    have hsum : A+1+A^2 ≤ A^3 := by nlinarith only [hA]
    have hP : A^3 ≤ A^(C+30) := pow_le_pow_right₀ hA1 (by omega)
    have hE : epsc+Mz*(lam*eps) ≤ (A+A^2)*(a*w) := by
      calc
        _ ≤ A*a*zeta+A^2*a*zeta := add_le_add hepscA hterm
        _ ≤ A*a*w+A^2*a*w := by gcongr
        _ = _ := by ring
    have hP1 : A+1+A^2 ≤ A^(C+30) := hsum.trans hP
    have hP2 : A^(C+30) ≤ (A-1)*A^(C+30) := by nlinarith only [hA,pow_nonneg hA0.le (C+30)]
    dsimp only [paddedError,errorPadding]
    calc
      _ ≤ (A+A^2)*(a*w)+A^(C+30)*(a*w) := by linarith
      _ ≤ ((A-1)*A^(C+30)+A^(C+30))*(a*w) := by
        rw [←add_mul]
        apply mul_le_mul_of_nonneg_right _ haw.le
        linarith only [hP1,hP2]
      _ = _ := by rw [pow_succ]; ring
  have hpad : errorPadding A C a w ≤ paddedError A C a w epsc Mz (lam*eps) := by
    dsimp only [paddedError]
    have hprod := mul_nonneg hMz hmesh0
    linarith only [hepsc,hprod]
  have hpadpos : 0 < errorPadding A C a w := by
    dsimp only [errorPadding]
    positivity
  have hwidth : a*w ≤ errorPadding A C a w := by
    dsimp only [errorPadding]
    exact le_mul_of_one_le_left haw.le (one_le_pow₀ hA1)
  have hfit19 : fit*(2*K)^19 ≤ A^20*(a*w) := by
    calc
      _ ≤ (A*(a*w))*A^19 := mul_le_mul hfit
        (pow_le_pow_left₀ (by positivity) hKA 19) (by positivity) (by positivity)
      _ = _ := by rw [pow_succ]; ring
  have hband : A^C*(fit*(2*K)^19) ≤ errorPadding A C a w := by
    calc
      _ ≤ A^C*(A^20*(a*w)) := by gcongr
      _ = A^(C+20)*(a*w) := by rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA1 (by omega : C+20 ≤ C+30)) haw.le
  have herrsmall : paddedError A C a w epsc Mz (lam*eps)*A^C ≤ 1 := by
    have haA : a ≤ A*zeta := by
      exact haK.trans ((mul_le_mul_of_nonneg_left hhzeta hK0.le).trans
        (mul_le_mul_of_nonneg_right hKle hzeta))
    calc
      _ ≤ (A^(C+31)*(a*w))*A^C := by gcongr
      _ ≤ (A^(C+31)*((A*zeta)*w))*A^C := by gcongr
      _ = (A^(2*C+32)*zeta)*w := by
        simp only [pow_add,pow_mul]
        ring
      _ ≤ w*w := mul_le_mul_of_nonneg_right (hsmall _ (by omega)) hw.le
      _ ≤ 1 := by nlinarith only [hw.le,hw1]
  refine {
    zeta_le_width := hzetaW
    mesh_nonneg := hmesh0
    mesh_half := hmeshW.trans (by linarith)
    mesh_accuracy := (hmesh C).trans ((hsmall _ (by omega)).trans hw1)
    mesh_covers_state := ?_
    error_pos := hpadpos.trans_le hpad
    padding_le_error := hpad
    width_le_error := hwidth.trans hpad
    error_upper := herr
    error_accuracy := herrsmall
    fit_input := ?_
    fit_in_tube := hband.trans hpad }
  · rw [div_le_iff₀ (by positivity : 0 < 8*K)]
    nlinarith only [hK,hmesh0]
  · calc
      _ ≤ A^20*(a*w) := hfit19
      _ ≤ A^(C+31)*(a*w) := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA1 (by omega)) haw.le
      _ = _ := by dsimp only [errorPadding]; rw [pow_succ']; ring

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
