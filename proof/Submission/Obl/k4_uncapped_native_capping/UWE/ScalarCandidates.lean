/-
Adapted from this LOT tree o198, session x0693, commit b5c1b640df5e526ffc014739d6614359923ec044,
Submission/Obl/k4_balanced_native_packet_transport/UWE/ScalarCandidates.lean. Existing source attributions below are retained.
-/
/-
Adapted from this LOT tree, o120, session x0649, commit 99e461c8faeab846d12253887b2a587a38b5aa0e,
Submission/Obl/k4_unbounded_width_exclusion/ScalarCandidates.lean (namespace Submission.Obl.k4_unbounded_width_exclusion renamed to
Submission.Obl.k4_uncapped_native_capping.UWE).
-/
import Submission.Obl.k4_uncapped_native_capping.UWE.Interface
import Submission.Lib.K4FinitePlankAtlases.Greedy

noncomputable section

namespace Submission.Obl.k4_uncapped_native_capping.UWE

open MeasureTheory Set Filter

def scalarY (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 0 + t * b 1

def scalarX (b : Fin 5 → ℝ) (t : ℝ) : ℝ := b 2 + t * b 3 + t ^ 2 * b 4

theorem scalarY_bound {z : Fin 5 → ℝ} {H t : ℝ}
    (hz : ∀ j, |z j| ≤ H) (ht : t ∈ Icc (0 : ℝ) 1) : |scalarY z t| ≤ 2 * H := by
  have ht' : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  calc
    _ ≤ |z 0| + |t * z 1| := abs_add_le _ _
    _ ≤ H + H := by rw [abs_mul]; nlinarith [abs_nonneg (z 1), hz 0, hz 1]
    _ = _ := by ring

def scalarCell (b : Fin 5 → ℝ) (t σ : ℝ) : Fin 2 → ℤ :=
  ![⌊t / σ⌋, ⌊scalarY b t / σ⌋]

/-- The geometric whole-block fit; it has no analytical density masks. -/
def scalarFit (P : MvPolynomial (Fin 2) ℝ) (error : ℝ) : Set (Fin 5 → ℝ) :=
  {b | ∀ t ∈ Icc (0 : ℝ) 1,
    |scalarX b t - MvPolynomial.eval ![t, scalarY b t] P| ≤ error}

theorem isClosed_scalarFit (P : MvPolynomial (Fin 2) ℝ) (error : ℝ) :
    IsClosed (scalarFit P error) := by
  have heq : scalarFit P error = ⋂ t : Icc (0 : ℝ) 1,
      {b | |scalarX b t - MvPolynomial.eval ![(t : ℝ), scalarY b t] P| ≤ error} := by
    ext b
    simp only [scalarFit, mem_ofPred_eq, mem_iInter]
    exact ⟨fun h t => h t t.property, fun h t ht => h ⟨t, ht⟩⟩
  rw [heq]
  apply isClosed_iInter
  intro t
  apply isClosed_le _ continuous_const
  dsimp only [scalarX, scalarY]
  apply Continuous.abs
  apply Continuous.sub (by fun_prop)
  exact P.continuous_eval.comp (by fun_prop)

def ScalarAdmissible {α : Type} [MeasurableSpace α]
    (N η d s m C S U c : ℝ) (ν : Measure α) (b : α → Fin 5 → ℝ)
    (μ : Measure (α × ℝ)) : Prop :=
  Measurable b ∧ IsProbabilityMeasure ν ∧
  μ ≤ ENNReal.ofReal (N ^ η) • (ν.prod volume) ∧
  μ (univ ×ˢ Icc (0 : ℝ) 1)ᶜ = 0 ∧
  (∀ l i, |b l i| ≤ N ^ η) ∧ N ^ (-C) ≤ c ∧ c ≤ N ^ C ∧
  (∀ (r : ℝ) (q : Fin 2 → ℤ) (j : ℤ), 0 ≤ r → r ≤ s →
    μ {p | scalarCell (b p.1) p.2 (N ^ (-m)) = q ∧
      ⌊scalarX (b p.1) p.2 / N ^ (-r)⌋ = j} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-r)) ^ d)) ∧
  (∃ F : Finset ((Fin 2 → ℤ) × ℤ),
    (F.card : ℝ) * (N ^ (-m)) ^ 2 ≤ N ^ η * c⁻¹ * (N ^ (-s)) ^ (-d) ∧
    ∀ᵐ p ∂μ, (scalarCell (b p.1) p.2 (N ^ (-m)),
      ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋) ∈ F) ∧
  (∀ (r : ℝ) (q : Fin 2 → ℤ) (j k : ℤ), 0 < r → r ≤ U →
    μ {p | scalarCell (b p.1) p.2 (N ^ (-m)) = q ∧
      ⌊scalarX (b p.1) p.2 / N ^ (-s)⌋ = j ∧
      ⌊b p.1 1 / N ^ (-r)⌋ = k} ≤
        ENNReal.ofReal (N ^ η * (N ^ (-m)) ^ 2 * c * (N ^ (-s)) ^ d * N ^ (-S * r)))

theorem ScalarAdmissible.mono {α : Type} [MeasurableSpace α]
    {N η d s m C S U c : ℝ} {ν : Measure α} {b : α → Fin 5 → ℝ}
    {μ μ' : Measure (α × ℝ)} (h : ScalarAdmissible N η d s m C S U c ν b μ)
    (hμ' : μ' ≤ μ) : ScalarAdmissible N η d s m C S U c ν b μ' := by
  obtain ⟨hb, hν, hdom, hsupp, hcoeff, hc₁, hc₂, hcap, hcover, hang⟩ := h
  obtain ⟨F, hFcard, hF⟩ := hcover
  refine ⟨hb, hν, hμ'.trans hdom, ?_, hcoeff, hc₁, hc₂, ?_,
    ⟨F, hFcard, ?_⟩, ?_⟩
  · exact le_antisymm ((hμ' _).trans_eq hsupp) bot_le
  · intro r q j hr hrs
    exact (hμ' _).trans (hcap r q j hr hrs)
  · exact ae_mono hμ' hF
  · intro r q j k hr hrU
    exact (hμ' _).trans (hang r q j k hr hrU)

theorem ScalarAdmissible.mono_loss {α : Type} [MeasurableSpace α]
    {N η η' d s m C S U c : ℝ} {ν : Measure α} {b : α → Fin 5 → ℝ}
    {μ : Measure (α × ℝ)} (h : ScalarAdmissible N η d s m C S U c ν b μ)
    (hN : 1 ≤ N) (hη : η ≤ η') : ScalarAdmissible N η' d s m C S U c ν b μ := by
  obtain ⟨hb, hν, hdom, hsupp, hcoeff, hc₁, hc₂, hcap, hcover, hang⟩ := h
  have hpow := Real.rpow_le_rpow_of_exponent_le hN hη
  have hN0 : 0 ≤ N := zero_le_one.trans hN
  have hc : 0 ≤ c := (Real.rpow_nonneg hN0 _).trans hc₁
  obtain ⟨F, hFcard, hF⟩ := hcover
  refine ⟨hb, hν, hdom.trans ?_, hsupp, fun l i => (hcoeff l i).trans hpow,
    hc₁, hc₂, ?_, ⟨F, hFcard.trans ?_, hF⟩, ?_⟩
  · intro E
    simp only [Measure.smul_apply, smul_eq_mul]
    gcongr
  · intro r q j hr hrs
    apply (hcap r q j hr hrs).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr
  · gcongr
  · intro r q j k hr hrU
    apply (hang r q j k hr hrU).trans
    apply ENNReal.ofReal_le_ofReal
    gcongr

theorem ScalarAdmissible.total_mass_le {α : Type} [MeasurableSpace α]
    {N η d s m C S U c : ℝ} {ν : Measure α} {b : α → Fin 5 → ℝ}
    {μ : Measure (α × ℝ)} (h : ScalarAdmissible N η d s m C S U c ν b μ) :
    μ univ ≤ ENNReal.ofReal (N ^ η) := by
  have := h.2.1
  have heq : μ univ = μ (univ ×ˢ Icc (0 : ℝ) 1) := by
    have hsum := measure_add_measure_compl (μ := μ)
      (s := (univ : Set α) ×ˢ Icc (0 : ℝ) 1)
      (MeasurableSet.univ.prod measurableSet_Icc)
    rw [h.2.2.2.1, add_zero] at hsum
    exact hsum.symm
  rw [heq]
  apply (h.2.2.1 _).trans
  simp [Measure.smul_apply, smul_eq_mul, Measure.prod_prod]

theorem ScalarAdmissible.isFiniteMeasure {α : Type} [MeasurableSpace α]
    {N η d s m C S U c : ℝ} {ν : Measure α} {b : α → Fin 5 → ℝ}
    {μ : Measure (α × ℝ)} (h : ScalarAdmissible N η d s m C S U c ν b μ) :
    IsFiniteMeasure μ :=
  ⟨lt_of_le_of_lt h.total_mass_le ENNReal.ofReal_lt_top⟩

/-- A scalar candidate stores only the polynomial and its adapted norm
witness. Its assignment is always the complete geometric fit. -/
structure ScalarCandidate (N s m ε : ℝ) where
  P : MvPolynomial (Fin 2) ℝ
  β : ℝ
  u : ℝ
  v : ℝ
  β_lower : N ^ (-ε) ≤ β
  β_upper : β ≤ N ^ ε
  center_bound : |u| + |v| ≤ N ^ ε
  degree : P.totalDegree ≤ 2
  adapted_bound : ∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
    |MvPolynomial.eval ![t, u + t * v + β * w] P| ≤ N ^ ε

def ScalarCandidate.fit {α : Type} [MeasurableSpace α]
    {N s m ε : ℝ} (F : ScalarCandidate N s m ε) (b : α → Fin 5 → ℝ) :
    Set (α × ℝ) := (b ⁻¹' scalarFit F.P (N ^ ε * N ^ (-s))) ×ˢ Icc 0 1

theorem ScalarCandidate.measurable_fit {α : Type} [MeasurableSpace α]
    {N s m ε : ℝ} (F : ScalarCandidate N s m ε) {b : α → Fin 5 → ℝ}
    (hb : Measurable b) : MeasurableSet (F.fit b) :=
  (hb (isClosed_scalarFit _ _).measurableSet).prod measurableSet_Icc

def scalarCandidateFloor (N c d s ε : ℝ) : ℝ :=
  c * (N ^ (-s)) ^ d * N ^ (-ε) / N ^ ε

/-- The mesh theorem gives a candidate with its mass measured against
the unnormalized input law and the fixed trajectory prior. -/
theorem scalar_candidate_of_mesh
    (hmesh : ScalarMeshProjection)
    {d s m C S U ε : ℝ} (hd : 0 ≤ d) (hd1 : d < 1)
    (hs : 0 < s) (hsm : s < m) (hC : 0 < C) (hS : 0 < S)
    (hU : 0 < U) (hUm : U < m) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∃ N₀ : ℝ, 2 ≤ N₀ ∧
      ∀ N : ℝ, N₀ ≤ N → ∀ (α : Type) [MeasurableSpace α]
        (ν : Measure α) (μ : Measure (α × ℝ)) (b : α → Fin 5 → ℝ) (c : ℝ),
        ScalarAdmissible N η d s m C S U c ν b μ →
        ENNReal.ofReal (N ^ (-η)) ≤ μ univ →
        ∃ F : ScalarCandidate N s m ε,
          ENNReal.ofReal (scalarCandidateFloor N c d s ε) ≤ μ (F.fit b) := by
  obtain ⟨η, hη, N₀, hN₀, hmesh⟩ := hmesh d s m C S U ε hd hd1 hs hsm hC hS hU hUm hε
  refine ⟨η, hη, N₀, hN₀, ?_⟩
  intro N hN α _ ν μ b c hadm hmass
  obtain ⟨hb, hν, hdom, hsupp, hcoeff, hc₁, hc₂, hcap, hcover, hang⟩ := hadm
  obtain ⟨n, β, A, u, v, P, hβ, hβup, hβlo, hA, hdisj, hpackets, hcovered⟩ :=
    hmesh N hN α ν μ b c true hb hν hdom hsupp hmass hcoeff hc₁ hc₂ hcap hcover
      (fun _ => hang)
  have hNpos : 0 < N := by linarith
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    have hempty : {p : α × ℝ | ∃ i : Fin 0, p.1 ∈ A i} = ∅ := by simp
    rw [hempty, measure_empty] at hcovered
    exact (not_le_of_gt (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hNpos _))) hcovered
  let i : Fin n := ⟨0, hn⟩
  let F : ScalarCandidate N s m ε :=
    ⟨P i, β, u i, v i, hβlo rfl, hβup, (hpackets i).1,
      (hpackets i).2.1, (hpackets i).2.2.1⟩
  refine ⟨F, ?_⟩
  have hfloor : scalarCandidateFloor N c d s ε ≤ c * (N ^ (-s)) ^ d * β / N ^ ε := by
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hNpos.le _)
    apply mul_le_mul_of_nonneg_left (hβlo rfl)
    apply mul_nonneg
    · exact le_trans (Real.rpow_nonneg hNpos.le _) hc₁
    · exact Real.rpow_nonneg (Real.rpow_nonneg hNpos.le _) _
  apply (ENNReal.ofReal_le_ofReal hfloor).trans
  apply (hpackets i).2.2.2.2.trans
  apply measure_mono
  intro p hp
  refine ⟨?_, hp.2⟩
  intro t ht
  exact ((hpackets i).2.2.2.1 p.1 hp.1 t ht).2

end Submission.Obl.k4_uncapped_native_capping.UWE
