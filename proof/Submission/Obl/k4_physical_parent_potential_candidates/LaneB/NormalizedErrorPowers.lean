import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.EventNumerator

namespace Submission.Obl.k4_physical_parent_potential_candidates.Analytic

noncomputable section

namespace NormalizedErrors

def hessianError (A Kt b hdelta s : ℝ) (J : ℕ) : ℝ :=
  (Kt*A^25*b+A^J*s*A^9*hdelta)/s

def potentialError (A Cq epsc Mz hdelta s m eta : ℝ) (J N : ℕ) : ℝ :=
  A^N*((A^J)^3*(epsc+Cq*Mz*A^3*hdelta)+Cq*Mz*(A^J)^2*eta)/(s*m)

def errorPower (J N : ℕ) : ℕ := N+4*J+40

def cutPower (J N C : ℕ) : ℕ := errorPower J N+C+5

/-- The smaller of the affine scale and the potential coefficient scale
controls the Hessian-test transfer term. -/
theorem weighted_hessian_error {A Kt b hdelta s epsc Mz : ℝ} (J : ℕ)
    (hA : 2 ≤ A) (hKt : 0 ≤ Kt) (hKtA : Kt ≤ A)
    (hb : 0 ≤ b) (hhdelta : 0 ≤ hdelta) (hs : 0 < s)
    (hepsc : 0 ≤ epsc) (hMz : 0 ≤ Mz) :
    min s Mz*hessianError A Kt b hdelta s J ≤
      A^(J+27)*(epsc+b+Mz*hdelta) := by
  let E := epsc+b+Mz*hdelta
  let t := min s Mz
  have hA0 : 0 < A := by linarith only [hA]
  have hA1 : 1 ≤ A := by linarith only [hA]
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hbE : b ≤ E := by
    dsimp only [E]
    linarith only [hepsc,mul_nonneg hMz hhdelta]
  have hME : Mz*hdelta ≤ E := by
    dsimp only [E]
    linarith only [hepsc,hb]
  have ht : 0 ≤ t := le_min hs.le hMz
  have hts : t/s ≤ 1 := (div_le_one hs).mpr (min_le_left _ _)
  have htM : t ≤ Mz := min_le_right _ _
  have hweighted : t*hessianError A Kt b hdelta s J ≤ A^26*b+A^(J+9)*(Mz*hdelta) := by
    have heq : t*hessianError A Kt b hdelta s J =
        (t/s)*(Kt*A^25*b)+A^(J+9)*(t*hdelta) := by
      dsimp only [hessianError]
      rw [pow_add]
      field_simp
      <;> ring
    rw [heq]
    apply add_le_add
    · calc
        _ ≤ 1*(A*A^25*b) := mul_le_mul hts
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hKtA (by positivity)) hb)
          (by positivity) (by positivity)
        _ = _ := by ring
    · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htM hhdelta) (by positivity)
  calc
    _ ≤ A^26*b+A^(J+9)*(Mz*hdelta) := hweighted
    _ ≤ A^(J+26)*E+A^(J+26)*E := add_le_add
      (mul_le_mul (pow_le_pow_right₀ hA1 (by omega)) hbE hb (by positivity))
      (mul_le_mul (pow_le_pow_right₀ hA1 (by omega)) hME (by positivity) (by positivity))
    _ ≤ A*(A^(J+26)*E) := by
      have hp : 2*(A^(J+26)*E) ≤ A*(A^(J+26)*E) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg (by positivity) hE)
      linarith only [hp]
    _ = _ := by dsimp only [E]; rw [pow_succ']; ring

/-- The direct graph estimate and the potential estimate together give a
bound linear in the unnormalized error, regardless of the affine scale. -/
theorem two_route_error {A Kt Cq b hdelta s epsc Mz m err : ℝ} (J N : ℕ)
    (hA : 2 ≤ A) (hKt : 0 ≤ Kt) (hKtA : Kt ≤ A)
    (hCq : 0 ≤ Cq) (hCqA : Cq ≤ A) (hb : 0 ≤ b) (hhdelta : 0 ≤ hdelta)
    (hs : 0 < s) (hepsc : 0 ≤ epsc) (hMz : 0 ≤ Mz)
    (hm : (A^2)⁻¹ ≤ m)
    (hpot : err ≤ potentialError A Cq epsc Mz hdelta s m
      (hessianError A Kt b hdelta s J) J N)
    (hdir : err ≤ A^N*(2*(A^J)^3*hessianError A Kt b hdelta s J)) :
    err ≤ A^errorPower J N*(epsc+b+Mz*hdelta)/s := by
  let E := epsc+b+Mz*hdelta
  let eta := hessianError A Kt b hdelta s J
  have hA0 : 0 < A := by linarith only [hA]
  have hA1 : 1 ≤ A := by linarith only [hA]
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hepsE : epsc ≤ E := by dsimp only [E]; linarith only [hb,mul_nonneg hMz hhdelta]
  have hME : Mz*hdelta ≤ E := by dsimp only [E]; linarith only [hepsc,hb]
  have heta : 0 ≤ eta := by dsimp only [eta,hessianError]; positivity
  have hweighted := weighted_hessian_error J hA hKt hKtA hb hhdelta hs hepsc hMz
  apply (le_div_iff₀ hs).mpr
  by_cases hsm : s ≤ Mz
  · have hsEta : s*eta ≤ A^(J+27)*E := by simpa only [min_eq_left hsm] using hweighted
    calc
      _ ≤ (A^N*(2*(A^J)^3*eta))*s := mul_le_mul_of_nonneg_right hdir hs.le
      _ = 2*A^(N+3*J)*(s*eta) := by simp only [pow_add,pow_mul]; ring
      _ ≤ A*A^(N+3*J)*(A^(J+27)*E) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hA (by positivity)) hsEta
          (mul_nonneg hs.le heta) (by positivity)
      _ = A^(N+4*J+28)*E := by simp only [pow_add,pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA1 (by dsimp only [errorPower]; omega)) hE

  · have hMs : Mz ≤ s := le_of_lt (lt_of_not_ge hsm)
    have hMEta : Mz*eta ≤ A^(J+27)*E := by simpa only [min_eq_right hMs] using hweighted
    have hm0 : 0 < m := (by positivity : 0 < (A^2)⁻¹).trans_le hm
    have hmI : m⁻¹ ≤ A^2 := by simpa only [inv_inv] using inv_anti₀ (by positivity : 0 < (A^2)⁻¹) hm
    have hbase : epsc+Cq*Mz*A^3*hdelta ≤ A^5*E := by
      have he : epsc ≤ A^4*E := hepsE.trans (le_mul_of_one_le_left hE (one_le_pow₀ hA1))
      have ht : Cq*Mz*A^3*hdelta ≤ A^4*E := by
        calc
          _ = (Cq*A^3)*(Mz*hdelta) := by ring
          _ ≤ (A*A^3)*E := mul_le_mul (mul_le_mul_of_nonneg_right hCqA (by positivity))
            hME (by positivity) (by positivity)
          _ = _ := by ring
      have hp : 2*(A^4*E) ≤ A*(A^4*E) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg (by positivity) hE)
      calc
        _ ≤ 2*(A^4*E) := by linarith only [he,ht]
        _ ≤ A*(A^4*E) := hp
        _ = _ := by ring
    have hnum : (A^J)^3*(epsc+Cq*Mz*A^3*hdelta)+Cq*Mz*(A^J)^2*eta ≤
        A^(3*J+29)*E := by
      have hfirst : (A^J)^3*(epsc+Cq*Mz*A^3*hdelta) ≤ A^(3*J+28)*E := by
        calc
          _ ≤ (A^J)^3*(A^5*E) := mul_le_mul_of_nonneg_left hbase (by positivity)
          _ = A^(3*J+5)*E := by simp only [pow_add,pow_mul]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 (by omega)) hE
      have hsecond : Cq*Mz*(A^J)^2*eta ≤ A^(3*J+28)*E := by
        calc
          _ = (Cq*(A^J)^2)*(Mz*eta) := by ring
          _ ≤ (A*(A^J)^2)*(A^(J+27)*E) :=
            mul_le_mul (mul_le_mul_of_nonneg_right hCqA (by positivity)) hMEta
              (mul_nonneg hMz heta) (by positivity)
          _ = _ := by simp only [pow_add,pow_mul]; ring
      have hp : 2*(A^(3*J+28)*E) ≤ A*(A^(3*J+28)*E) :=
        mul_le_mul_of_nonneg_right hA (mul_nonneg (by positivity) hE)
      calc
        _ ≤ 2*(A^(3*J+28)*E) := by linarith only [hfirst,hsecond]
        _ ≤ A*(A^(3*J+28)*E) := hp
        _ = _ := by rw [pow_succ']; ring
    calc
      _ ≤ potentialError A Cq epsc Mz hdelta s m eta J N*s :=
        mul_le_mul_of_nonneg_right hpot hs.le
      _ = A^N*((A^J)^3*(epsc+Cq*Mz*A^3*hdelta)+Cq*Mz*(A^J)^2*eta)*m⁻¹ := by
        dsimp only [potentialError]
        field_simp
        <;> ring
      _ ≤ A^N*(A^(3*J+29)*E)*A^2 := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hnum (by positivity)
        · exact hmI
        · exact inv_nonneg.mpr hm0.le
        · positivity
      _ = A^(N+3*J+31)*E := by simp only [pow_add,pow_mul]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ hA1 (by dsimp only [errorPower]; omega)) hE

theorem hessian_error_le {A Kt b hdelta s : ℝ} (J : ℕ)
    (hA : 0 ≤ A) (hKt : 0 ≤ Kt) (hKtA : Kt ≤ A)
    (hb : 0 ≤ b) (hhdelta : 0 ≤ hdelta) (hs : 0 < s) :
    hessianError A Kt b hdelta s J ≤ A^26*b/s+A^(J+9)*hdelta := by
  have heq : hessianError A Kt b hdelta s J = Kt*A^25*b/s+A^(J+9)*hdelta := by
    dsimp only [hessianError]
    rw [pow_add]
    field_simp
    <;> ring
  rw [heq]
  apply add_le_add
  · apply div_le_div_of_nonneg_right _ hs.le
    calc
      _ ≤ A*A^25*b := by gcongr
      _ = _ := by ring
  · exact le_rfl

/-- Cutting at a fixed power times the total error simultaneously makes
the Hessian and cleared cubic tests small enough for branch restoration. -/
theorem accuracy_from_cutoff {A Kt b hdelta s epsc Mz : ℝ} (J N C CW : ℕ)
    (hA : 2 ≤ A) (hKt : 0 ≤ Kt) (hKtA : Kt ≤ A)
    (hb : 0 < b) (hhdelta : 0 ≤ hdelta) (hepsc : 0 ≤ epsc) (hMz : 0 ≤ Mz)
    (hcutCW : cutPower J N C ≤ CW) (hmeshCW : J+C+10 ≤ CW)
    (hmesh : hdelta*A^CW ≤ 1) (herror : (epsc+b+Mz*hdelta)*A^CW ≤ 1)
    (hcut : A^cutPower J N C*(epsc+b+Mz*hdelta) ≤ s) :
    0 < s ∧ A^cutPower J N C*(epsc+b+Mz*hdelta) ≤ 1 ∧
      epsc+b+Mz*hdelta ≤ s ∧
      hessianError A Kt b hdelta s J*A^C ≤ 1 ∧
      (A^errorPower J N*(epsc+b+Mz*hdelta)/s)*A^C ≤ 1 := by
  let E := epsc+b+Mz*hdelta
  have hA0 : 0 < A := by linarith only [hA]
  have hA1 : 1 ≤ A := by linarith only [hA]
  have hE : 0 < E := by dsimp only [E]; positivity
  have hbE : b ≤ E := by dsimp only [E]; linarith only [hepsc,mul_nonneg hMz hhdelta]
  have hEs : E ≤ s :=
    (le_mul_of_one_le_left hE.le (one_le_pow₀ hA1)).trans hcut
  have hs : 0 < s := hE.trans_le hEs
  have hcutSmall : A^cutPower J N C*E ≤ 1 := by
    calc
      _ ≤ A^CW*E := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 hcutCW) hE.le
      _ ≤ _ := by simpa only [E,mul_comm] using herror
  have hfirst : (A^26*b/s)*A^C ≤ 1/2 := by
    have hnum : 2*(A^(C+26)*b) ≤ s := by
      calc
        _ ≤ A*(A^(C+26)*E) := mul_le_mul hA
          (mul_le_mul_of_nonneg_left hbE (by positivity)) (by positivity) hA0.le
        _ = A^(C+27)*E := by rw [pow_succ']; ring
        _ ≤ A^cutPower J N C*E := mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ hA1 (by dsimp only [cutPower,errorPower]; omega)) hE.le
        _ ≤ _ := hcut
    have heq : (A^26*b/s)*A^C = A^(C+26)*b/s := by rw [pow_add]; ring
    rw [heq,div_le_iff₀ hs]
    linarith only [hnum]
  have hsecond : (A^(J+9)*hdelta)*A^C ≤ 1/2 := by
    have hprod : A*((A^(J+9)*hdelta)*A^C) ≤ 1 := by
      calc
        _ = hdelta*A^(J+C+10) := by simp only [pow_add,pow_succ']; ring
        _ ≤ hdelta*A^CW := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hA1 hmeshCW) hhdelta
        _ ≤ _ := hmesh
    have h2 : 2*((A^(J+9)*hdelta)*A^C) ≤ A*((A^(J+9)*hdelta)*A^C) :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    linarith only [hprod,h2]
  refine ⟨hs,hcutSmall,hEs,?_,?_⟩
  · have hh := mul_le_mul_of_nonneg_right
      (hessian_error_le J hA0.le hKt hKtA hb.le hhdelta hs) (by positivity : 0 ≤ A^C)
    linarith only [hh,hfirst,hsecond]
  · have hnum : A^(errorPower J N+C)*E ≤ s :=
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1
        (by dsimp only [cutPower]; omega)) hE.le).trans hcut
    have heq : (A^errorPower J N*E/s)*A^C = A^(errorPower J N+C)*E/s := by
      rw [pow_add]
      ring
    rw [heq]
    exact (div_le_one hs).mpr hnum

end NormalizedErrors

end

end Submission.Obl.k4_physical_parent_potential_candidates.Analytic
