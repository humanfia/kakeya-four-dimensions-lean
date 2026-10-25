/-
Adapted from: here:root
Original proofs by session x0001.
-/
import Submission.Lib.K4PolynomialNorming.KernelDomination

open Set MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

namespace Submission.Lib.K4PolynomialNorming

noncomputable abbrev fullHistoryMarkovKernel {Ω : Type*} [MeasurableSpace Ω]
    (K : ℕ → Kernel Ω Ω) (n : ℕ) : Kernel ((i : Finset.Iic n) → Ω) Ω :=
  (K n).comap (fun h : (i : Finset.Iic n) → Ω => h ⟨n, by simp⟩) (by fun_prop)

/-- The ordinary path law, before restricting to any successful paths. -/
noncomputable def kernelPathMeasure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (K : ℕ → Kernel Ω Ω) [∀ n, IsMarkovKernel (K n)] :
    Measure (ℕ → Ω) := Kernel.trajMeasure P (fullHistoryMarkovKernel K)

theorem kernelPathMeasure_isProbability {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] : IsProbabilityMeasure (kernelPathMeasure P K) := by
  unfold kernelPathMeasure
  infer_instance

attribute [local instance] kernelPathMeasure_isProbability

theorem kernelPathMeasure_map_zero {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] : (kernelPathMeasure P K).map (fun x => x 0) = P := by
  have hprefix : (kernelPathMeasure P K).map
      (Preorder.frestrictLe (π := fun _ : ℕ => Ω) 0) =
      P.map (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Ω)).symm := by
    rw [kernelPathMeasure, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
      Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
  have hfun : (fun x : ℕ → Ω => x 0) =
      (fun h : (i : Finset.Iic 0) → Ω => h ⟨0, by simp⟩) ∘ Preorder.frestrictLe 0 := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), hprefix,
    Measure.map_map (by fun_prop) (by fun_prop)]
  change P.map id = P
  simp

theorem kernelPathMeasure_map_succ {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (kernelPathMeasure P K).map (fun x => x (n + 1)) =
      K n ∘ₘ (kernelPathMeasure P K).map (fun x => x n) := by
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Ω) (μ₀ := P) (κ := fullHistoryMarkovKernel K) (a := n)
  have h := congrArg (fun μ : Measure (((i : Finset.Iic n) → Ω) × Ω) => μ.map Prod.snd) hjoint
  change (((kernelPathMeasure P K).map (Preorder.frestrictLe n)) ⊗ₘ
    fullHistoryMarkovKernel K n).snd = _ at h
  rw [Measure.snd_compProd, Measure.map_map (by fun_prop) (by fun_prop)] at h
  change ((K n).comap (fun h : (i : Finset.Iic n) → Ω => h ⟨n, by simp⟩) (by fun_prop)) ∘ₘ
      ((kernelPathMeasure P K).map (Preorder.frestrictLe n)) = _ at h
  rw [← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h.symm

/-- Each step may use a different transition; preservation of the original
prior is what gives the same marginal at every time. -/
theorem kernelPathMeasure_stationary_marginal {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ P = P) (n : ℕ) :
    (kernelPathMeasure P K).map (fun x => x n) = P := by
  induction n with
  | zero => exact kernelPathMeasure_map_zero P K
  | succ n ih => rw [kernelPathMeasure_map_succ, ih, hK n]

/-- All finitely many good observations retain an explicit original-law
mass. No independence or post-success resampling is assumed. -/
theorem kernelPathMeasure_good_path_mass {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ P = P) (N : ℕ)
    (G : Fin (N + 1) → Set Ω) (hG : ∀ i, MeasurableSet (G i)) :
    (1 : ENNReal) ≤ (kernelPathMeasure P K) {x | ∀ i : Fin (N + 1), x i ∈ G i} +
      ∑ i : Fin (N + 1), P ((G i)ᶜ) := by
  let Q := kernelPathMeasure P K
  have hbad (i : Fin (N + 1)) : Q {x | x i ∉ G i} = P ((G i)ᶜ) := by
    rw [← kernelPathMeasure_stationary_marginal P K hK (i : ℕ),
      Measure.map_apply (by fun_prop) (hG i).compl]
    rfl
  have hsum : Q (⋃ i : Fin (N + 1), {x | x i ∉ G i}) ≤ ∑ i : Fin (N + 1), P ((G i)ᶜ) := by
    calc
      _ ≤ ∑ i : Fin (N + 1), Q {x | x i ∉ G i} := measure_iUnion_fintype_le _ _
      _ = _ := Finset.sum_congr rfl (fun i _ => hbad i)
  have hcover : (Set.univ : Set (ℕ → Ω)) ⊆
      {x | ∀ i : Fin (N + 1), x i ∈ G i} ∪ ⋃ i : Fin (N + 1), {x | x i ∉ G i} := by
    intro x _
    by_cases hx : ∀ i : Fin (N + 1), x i ∈ G i
    · exact Or.inl hx
    · obtain ⟨i, hi⟩ := not_forall.mp hx
      exact Or.inr (Set.mem_iUnion.mpr ⟨i, hi⟩)
  calc
    _ = Q Set.univ := by simp [Q]
    _ ≤ Q ({x | ∀ i : Fin (N + 1), x i ∈ G i} ∪ ⋃ i : Fin (N + 1), {x | x i ∉ G i}) :=
      measure_mono hcover
    _ ≤ Q {x | ∀ i : Fin (N + 1), x i ∈ G i} + Q (⋃ i : Fin (N + 1), {x | x i ∉ G i}) :=
      measure_union_le _ _
    _ ≤ _ := add_le_add le_rfl hsum

/-- For separated measurable observations, the Dirac pushforward property
of conditional refresh gives literal equality of the refreshed code. -/
theorem conditionalRefresh_code_ae_eq {Ω S : Type*} [MeasurableSpace Ω]
    [StandardBorelSpace Ω] [Nonempty Ω] [MeasurableSpace S]
    [MeasurableSpace.CountablyGenerated S] [MeasurableSingletonClass S]
    (P : Measure Ω) [IsFiniteMeasure P] (g : Ω → S) (hg : Measurable g) :
    ∀ᵐ x ∂P, ∀ᵐ y ∂conditionalRefresh P g hg x, g y = g x := by
  filter_upwards [conditionalRefresh_preserves_code P g hg] with x hx
  have ha : ∀ᵐ s ∂(conditionalRefresh P g hg x).map g, s = g x := by
    rw [hx]
    simp
  exact ae_of_ae_map hg.aemeasurable ha

theorem map_compProd_comap {X Y Z : Type*}
    [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) [IsFiniteMeasure μ] (κ : Kernel Y Z) [IsSFiniteKernel κ]
    (f : X → Y) (hf : Measurable f) :
    (μ ⊗ₘ κ.comap f hf).map (fun z : X × Z => (f z.1,z.2)) = μ.map f ⊗ₘ κ := by
  ext E hE
  have hmap : Measurable (fun z : X × Z => (f z.1,z.2)) :=
    (hf.comp measurable_fst).prodMk measurable_snd
  have hg : Measurable (fun y : Y => κ y (Prod.mk y ⁻¹' E)) :=
    Kernel.measurable_kernel_prodMk_left hE
  rw [Measure.map_apply hmap hE, Measure.compProd_apply (hmap hE),
    Measure.compProd_apply hE, lintegral_map hg hf]
  rfl

/-- Consecutive states have the actual Markov coupling, without replacing
that coupling by a product of marginals. -/
theorem kernelPathMeasure_pair_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (kernelPathMeasure P K).map (fun x => (x n,x (n+1))) =
      (kernelPathMeasure P K).map (fun x => x n) ⊗ₘ K n := by
  let f : ((i : Finset.Iic n) → Ω) → Ω := fun h => h ⟨n, by simp⟩
  have hf : Measurable f := by fun_prop
  have hproj : ((kernelPathMeasure P K).map (Preorder.frestrictLe n)).map f =
      (kernelPathMeasure P K).map (fun x => x n) := by
    rw [Measure.map_map hf (by fun_prop)]
    rfl
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (X := fun _ : ℕ => Ω) (μ₀ := P) (κ := fullHistoryMarkovKernel K) (a := n)
  have h := congrArg (fun μ : Measure (((i : Finset.Iic n) → Ω) × Ω) =>
    μ.map (fun z => (f z.1,z.2))) hjoint
  change ((((kernelPathMeasure P K).map (Preorder.frestrictLe n)) ⊗ₘ
    (K n).comap f hf).map (fun z => (f z.1,z.2))) = _ at h
  rw [map_compProd_comap _ (K n) f hf, hproj,
    Measure.map_map (by fun_prop) (by fun_prop)] at h
  exact h.symm

theorem kernelPathMeasure_stationary_pair_law {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ P = P) (n : ℕ) :
    (kernelPathMeasure P K).map (fun x => (x n,x (n+1))) = P ⊗ₘ K n := by
  rw [kernelPathMeasure_pair_law, kernelPathMeasure_stationary_marginal P K hK n]

/-- An original-prior almost-sure transition property holds at each
actual path leg, before any successful-path restriction. -/
theorem kernelPathMeasure_ae_step {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (K : ℕ → Kernel Ω Ω)
    [∀ n, IsMarkovKernel (K n)] (hK : ∀ n, K n ∘ₘ P = P) (n : ℕ)
    (R : Set (Ω × Ω)) (hR : MeasurableSet R)
    (hstep : ∀ᵐ x ∂P, ∀ᵐ y ∂K n x, (x,y) ∈ R) :
    ∀ᵐ x ∂kernelPathMeasure P K, (x n,x (n+1)) ∈ R := by
  have h : ∀ᵐ z ∂P ⊗ₘ K n, z ∈ R := Measure.ae_compProd_of_ae_ae hR hstep
  rw [← kernelPathMeasure_stationary_pair_law P K hK n] at h
  exact ae_of_ae_map (by fun_prop) h

end Submission.Lib.K4PolynomialNorming
