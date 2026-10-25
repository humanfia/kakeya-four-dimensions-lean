-- Adapted from this LOT tree, o173, session x0598, commit 73bbfb73,
-- Submission/Obl/k4_quadratic_cover_to_analytical_atlas/Directional.lean (namespace renamed).

import Submission.Obl.k4_clean_cover_graph_atlas.Matching
import Submission.Obl.k4_algebraic_real_jet_comparison

namespace Submission.Obl.k4_clean_cover_graph_atlas

open Set Metric Finset

/-- A real-on-real algebraic sheet on the fixed comparison domain. -/
structure RealSheet (D : ℕ) where
  f : Complex3 → ℂ
  P : MvPolynomial (Fin 4) ℂ
  nonzero : P ≠ 0
  degree : P.totalDegree ≤ D
  holomorphic : DifferentiableOn ℂ f (ball 0 4)
  equation : ∀ z ∈ ball (0 : Complex3) 4,
    MvPolynomial.eval (Fin.snoc (fun j : Fin 3 => z j) (f z)) P = 0
  real_on_real : ∀ x : Real3, ‖x‖ ≤ 1 → (f (emb x)).im = 0

/-- Center directional jets, recorded as an ordinary finite vector of real numbers. -/
noncomputable def directionalJets (V : Finset Real3) (K : ℕ) (f : Complex3 → ℂ) :
    (V × Fin (K + 1)) → ℝ :=
  fun i => iteratedDeriv i.2.val (fun t : ℝ => (f (emb (t • i.1.val))).re) 0

/-- Derivatives of sheet differences equal the differences of the recorded derivatives. -/
theorem directional_deriv_sub {f g : Complex3 → ℂ}
    (hf : DifferentiableOn ℂ f (ball 0 4)) (hg : DifferentiableOn ℂ g (ball 0 4))
    (v : Real3) (hv : ‖v‖ ≤ 1) (m : ℕ) :
    iteratedDeriv m (fun t : ℝ => (f (emb (t • v)) - g (emb (t • v))).re) 0 =
      iteratedDeriv m (fun t : ℝ => (f (emb (t • v))).re) 0 -
      iteratedDeriv m (fun t : ℝ => (g (emb (t • v))).re) 0 := by
  have he (t : ℝ) : emb (t • v) = (0 : Complex3) + (t : ℂ) • emb v := by
    simpa only [zero_add, map_zero] using
      Submission.Obl.k4_algebraic_real_jet_comparison.realEmbedding_line (0 : Real3) v t
  have hs (q : Complex3 → ℂ) (hq : DifferentiableOn ℂ q (ball 0 4)) :
      ContDiffAt ℝ m (fun t : ℝ => (q (emb (t • v))).re) 0 := by
    simp_rw [he]
    apply (Submission.Obl.k4_algebraic_real_jet_comparison.contDiffOn_real_line hq
      0 (emb v) (by norm_num) (by simpa using hv) m).contDiffAt
    exact isOpen_Ioo.mem_nhds (by norm_num)
  simp only [Complex.sub_re]
  exact iteratedDeriv_fun_sub (hs f hf) (hs g hg)

/-- The accepted real jet comparison supplies one finite system that controls the norm
of every pair of sheets of the prescribed degree, and bounds neighboring labels from
norm proximity. All its constants are chosen before any candidate family. -/
theorem exists_directional_jet_system (D : ℕ) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ V : Finset Real3, (∀ v ∈ V, ‖v‖ = 1) ∧
      ∃ c : ℝ, 0 < c ∧ ∃ B : ℕ → ℝ, (∀ m, 0 < B m) ∧
      ∀ f g : RealSheet D,
        (∀ x : Real3, ‖x‖ ≤ (1 : ℝ) / 2 →
          c * ‖f.f (emb x) - g.f (emb x)‖ ≤
            ∑ i : V × Fin (K + 1),
              |directionalJets V K f.f i - directionalJets V K g.f i|) ∧
        (∀ A : ℝ, 0 < A →
          (∀ x : Real3, ‖x‖ ≤ 1 → ‖f.f (emb x) - g.f (emb x)‖ ≤ A) →
          ∀ i : V × Fin (K + 1),
            |directionalJets V K f.f i - directionalJets V K g.f i| ≤ B i.2.val * A) := by
  classical
  obtain ⟨K, hK, V, hV, c, hc, B, hB, hcompare⟩ :=
    Submission.k4_algebraic_real_jet_comparison D
  refine ⟨K, hK, V, hV, c, hc, B, hB, ?_⟩
  intro f g
  obtain ⟨-, -, hupper, hlower⟩ := hcompare f.f g.f f.P g.P f.nonzero g.nonzero
    f.degree g.degree f.holomorphic g.holomorphic f.equation g.equation
    (fun x hx => ⟨f.real_on_real x hx, g.real_on_real x hx⟩)
  have hj (v : V) (j : ℕ) :
      iteratedDeriv j
        (fun t : ℝ => (f.f (emb ((0 : Real3) + t • v.val)) -
          g.f (emb ((0 : Real3) + t • v.val))).re) 0 =
        iteratedDeriv j (fun t : ℝ => (f.f (emb (t • v.val))).re) 0 -
          iteratedDeriv j (fun t : ℝ => (g.f (emb (t • v.val))).re) 0 := by
    simpa only [zero_add] using directional_deriv_sub f.holomorphic g.holomorphic
      v.val (hV v.val v.property).le j
  constructor
  · intro x hx
    have hl := hlower 0 x (by norm_num) hx
    calc
      _ ≤ ∑ v ∈ V, ∑ j ∈ range (K + 1),
          |iteratedDeriv j (fun t : ℝ =>
            (f.f (emb ((0 : Real3) + t • v)) - g.f (emb ((0 : Real3) + t • v))).re) 0| := hl
      _ = _ := by
        rw [Fintype.sum_prod_type, ← sum_coe_sort]
        apply sum_congr rfl
        intro v _
        rw [← Fin.sum_univ_eq_sum_range]
        apply sum_congr rfl
        intro j _
        rw [hj]
        rfl
  · intro A hA hbound i
    have hu := hupper A hA hbound i.1.val i.1.property i.2.val 0 (by norm_num)
    change |iteratedDeriv i.2.val (fun t : ℝ =>
      (f.f (emb ((0 : Real3) + t • i.1.val)) -
        g.f (emb ((0 : Real3) + t • i.1.val))).re) 0| ≤ B i.2.val * A at hu
    rw [hj] at hu
    exact hu

end Submission.Obl.k4_clean_cover_graph_atlas
