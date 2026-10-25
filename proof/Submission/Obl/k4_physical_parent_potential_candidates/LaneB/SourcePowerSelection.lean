import Submission.Obl.k4_native_finite_terminal_atlas_lift.LiftBounds
import Submission.Obl.k4_physical_parent_potential_candidates.LaneB.SourcePowerGeometry

namespace Submission.Obl.k4_physical_parent_potential_candidates

noncomputable section

namespace SourceNormalization

/-- The exponent is chosen before the source constant. -/
theorem exists_uniform_constant_power (C : ℝ) :
    ∃ m : ℕ, ∀ K : ℝ, 2 ≤ K → C ≤ K^m := by
  obtain ⟨m,hm⟩ := pow_unbounded_of_one_lt C (by norm_num : (1:ℝ) < 2)
  exact ⟨m,fun K hK => hm.le.trans (pow_le_pow_left₀ (by norm_num) hK m)⟩

/-- The actual discriminant bound and the initial native derivative scale
are dominated by one fixed source power, uniformly over all packets. -/
theorem exists_initial_source_power (q : ℕ) {Cden Cq : ℝ}
    (hCden : 1 ≤ Cden) (hCq : 0 < Cq) :
    ∃ I : ℕ, 200 ≤ I ∧ ∀ K : ℝ, 2 ≤ K →
      2 ≤ K^I ∧ 2*(2*K)^2 ≤ (K^I)^2 ∧
      Cq*(32*(((2*q:ℕ):ℝ)+1)*((Cden*K^209)*(8*K)^3))^(3*(2*q))*
        ((2*K)^2+1) ≤ K^I := by
  let L : ℝ := 16384*(((2*q:ℕ):ℝ)+1)*Cden
  let C : ℝ := Cq*L^(6*q)*5
  let n : ℕ := 212*(6*q)+2
  obtain ⟨s,hs⟩ := pow_unbounded_of_one_lt C (by norm_num : (1:ℝ) < 2)
  let I : ℕ := n+s+200
  refine ⟨I,by dsimp only [I]; omega,?_⟩
  intro K hK
  have hK0 : 0 < K := by linarith
  have hK1 : 1 ≤ K := by linarith
  have hI : 200 ≤ I := by dsimp only [I]; omega
  obtain ⟨hAR,_,hvel,_⟩ := power_frame_bounds hK hI
  have h4K : 4*K ≤ K^I := by
    have h4 : (4:ℝ) ≤ K^2 := by nlinarith only [hK]
    calc
      _ ≤ K^2*K := mul_le_mul_of_nonneg_right h4 hK0.le
      _ = K^3 := by ring
      _ ≤ _ := pow_le_pow_right₀ hK1 (by dsimp only [I]; omega)
  have hA1 : 2*(2*K)^2 ≤ (K^I)^2 := by
    have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 4*K) h4K 2
    nlinarith only [hp,sq_nonneg K]
  refine ⟨hAR,hA1,?_⟩
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hbase : 32*(((2*q:ℕ):ℝ)+1)*((Cden*K^209)*(8*K)^3) = L*K^212 := by
    dsimp only [L]
    ring
  have htail : (2*K)^2+1 ≤ 5*K^2 := by
    have hp : 1 ≤ K^2 := one_le_pow₀ hK1
    nlinarith only [hp]
  have hbound : Cq*(32*(((2*q:ℕ):ℝ)+1)*((Cden*K^209)*(8*K)^3))^(3*(2*q))*
      ((2*K)^2+1) ≤ C*K^n := by
    rw [hbase,show 3*(2*q)=6*q by omega,mul_pow]
    calc
      _ ≤ Cq*(L^(6*q)*(K^212)^(6*q))*(5*K^2) := by gcongr
      _ = _ := by dsimp only [C,n]; rw [pow_add,pow_mul]; ring
  have habsorb := Submission.Obl.k4_native_finite_terminal_atlas_lift.power_absorbs_constant
    hK n s hs.le
  exact hbound.trans (habsorb.trans (pow_le_pow_right₀ hK1 (by dsimp only [I]; omega)))

/-- All remaining source, zoom, coefficient and relative-density constants
are controlled by one common power, fixed before any packet is supplied. -/
theorem exists_final_source_power (q I qz Mexp : ℕ) (Ab Cx Cjet Cden : ℝ) :
    ∃ M : ℕ, 200 ≤ M ∧ ∀ K : ℝ, 2 ≤ K →
      Ab ≤ K^M ∧ Cx+1 ≤ K^M ∧ 512*Cjet*K^3 ≤ K^M ∧
      (((((q+1)^3:ℕ):ℝ)^2)*K*(18*K)^q) ≤ K^M ∧
      ((K^I)^qz)^Mexp ≤ K^M ∧
      ((K^I)^qz)^(3*(1+(Mexp+1))+14) ≤ K^M ∧
      ((Cden*K^209)*(8*K)^3)*((K^I)^qz)^(3*(1+(Mexp+1))+14) ≤ K^M := by
  let L : ℕ := I*qz*Mexp
  let Z : ℕ := I*qz*(3*(1+(Mexp+1))+14)
  let Cp : ℝ := ((((q+1)^3:ℕ):ℝ)^2)*18^q
  let Cf : ℝ := max Ab (max (Cx+1) (max (512*Cjet) (max Cp (512*Cden))))
  obtain ⟨s,hs⟩ := pow_unbounded_of_one_lt Cf (by norm_num : (1:ℝ) < 2)
  let M : ℕ := 400+s+q+1+L+Z
  refine ⟨M,by dsimp only [M]; omega,?_⟩
  intro K hK
  have hK1 : 1 ≤ K := by linarith
  have hc (b : ℝ) (hb : b ≤ Cf) (n : ℕ) (hn : n+s ≤ M) : b*K^n ≤ K^M := by
    exact (Submission.Obl.k4_native_finite_terminal_atlas_lift.power_absorbs_constant
      hK n s (hb.trans hs.le)).trans (pow_le_pow_right₀ hK1 hn)
  have hAb : Ab ≤ Cf := le_max_left _ _
  have hCx : Cx+1 ≤ Cf := (le_max_left _ _).trans (le_max_right _ _)
  have hCj : 512*Cjet ≤ Cf :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hCp : Cp ≤ Cf :=
    (le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hCd : 512*Cden ≤ Cf :=
    (le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  have hLam : ((K^I)^qz)^Mexp = K^L := by
    dsimp only [L]
    simp only [←pow_mul,Nat.mul_assoc]
  have hZ : ((K^I)^qz)^(3*(1+(Mexp+1))+14) = K^Z := by
    dsimp only [Z]
    simp only [←pow_mul,Nat.mul_assoc]
  refine ⟨by simpa using hc Ab hAb 0 (by dsimp only [M]; omega),
    by simpa using hc (Cx+1) hCx 0 (by dsimp only [M]; omega),
    hc _ hCj 3 (by dsimp only [M]; omega),?_,?_,?_,?_⟩
  · have heq : (((((q+1)^3:ℕ):ℝ)^2)*K*(18*K)^q) = Cp*K^(q+1) := by
      dsimp only [Cp]
      rw [mul_pow,pow_succ]
      ring
    rw [heq]
    exact hc _ hCp (q+1) (by dsimp only [M]; omega)
  · change ((K^I)^qz)^Mexp ≤ K^M
    rw [hLam]
    exact pow_le_pow_right₀ hK1 (by dsimp only [M]; omega)
  · rw [hZ]
    exact pow_le_pow_right₀ hK1 (by dsimp only [M]; omega)
  · rw [hZ]
    have heq : (Cden*K^209*(8*K)^3)*K^Z = (512*Cden)*K^(212+Z) := by
      rw [pow_add]
      ring
    rw [heq]
    exact hc _ hCd (212+Z) (by dsimp only [M,L]; omega)

end SourceNormalization

end

end Submission.Obl.k4_physical_parent_potential_candidates
