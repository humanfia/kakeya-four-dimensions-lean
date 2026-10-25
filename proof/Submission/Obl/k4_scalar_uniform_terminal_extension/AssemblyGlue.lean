import Submission.Obl.k4_scalar_uniform_terminal_extension.PairInterface

namespace Submission.Obl.k4_scalar_uniform_terminal_extension

/-- Uniform comparison and finite atlas assembly give the required fixed-depth extension. -/
theorem extension_of_pair_certificates (hpairs : AngularPairs) (hassembly : PairAssembly) :
    Extension := by
  intro d₀ S₀ η _hd₀ _hd₁ hS hη
  obtain ⟨a, c, ha, hc, hpair⟩ := hpairs S₀ η hS hη
  let C : ℝ := a + 10
  have hC : 0 < C := by dsimp [C]; linarith
  let c' : ℝ := min c (1 / (2 * C))
  have hc' : 0 < c' := lt_min hc (by positivity)
  refine ⟨C, c', hC, hc', ?_⟩
  intro p hp _hd hSp hUp h e hh hcost he heh hec
  have hL : 0 < L p := hp.1.2.2.2.2.2.1
  have hec₀ : e < c * L p :=
    hec.trans_le (mul_le_mul_of_nonneg_right (min_le_left _ _) hL.le)
  have hesmall : e < (1 / (2 * C)) * L p :=
    hec.trans_le (mul_le_mul_of_nonneg_right (min_le_right _ _) hL.le)
  have hediv : e < L p / (2 * C) := by
    simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hesmall
  have heprod : e * (2 * C) < L p :=
    (lt_div_iff₀ (by positivity : 0 < 2 * C)).mp hediv
  have hCe : 0 < C * e := mul_pos hC he
  have hr : 0 < L p - C * e := by linarith
  refine ⟨L p - C * e, hr, by linarith, by linarith, ?_⟩
  exact hassembly p hp h e a he heh ha hr
    (hpair p hp hSp hUp h e hh hcost he heh hec₀)

end Submission.Obl.k4_scalar_uniform_terminal_extension
