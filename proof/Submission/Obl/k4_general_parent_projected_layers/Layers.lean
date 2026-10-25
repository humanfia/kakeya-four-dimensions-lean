import Submission.Obl.k4_general_parent_projected_layers.Model

/-!
# Projected layers: the single-depth interface and its finite assembly

`SingleLayer` is the single-depth projection step, uniform over dense
submeasures of the original residual (the general-observable analogue of the
accepted o226 `SingleProjection`). `OrdinaryPreparation` asks for it at every
depth of `[a, 2a]` with one constant `L`.

From these, `exists_layers_of_single` selects layers successively at every depth
of a finite set, on a common dense residual, and then a diagonal subsequence with
one subpower loss. All floors stay charged to the original residual; the
reference budget follows from the floors, disjointness and `ρ univ ≤ K`.
-/

namespace Submission.Obl.k4_general_parent_projected_layers

open MeasureTheory Set Filter MvPolynomial

noncomputable section

/-- One finite disjoint family of full-time projected quadratic predictions at one depth. -/
structure ProjLayer (α : Type) where
  n : ℕ
  β : ℝ
  C : Fin n → Set α
  tag : Fin n → Fin 2 → ℤ
  u : Fin n → ℝ
  v : Fin n → ℝ
  G : Fin n → MvPolynomial (Fin 2) ℝ

namespace ProjLayer

variable {α : Type} [MeasurableSpace α]

/-- The empty layer. -/
def empty : ProjLayer α := ⟨0, 1, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0, Fin.elim0⟩

/-- Its coverage, as an incidence event. -/
def covered (L : ProjLayer α) : Set (α × ℝ) := {z | ∃ i, z.1 ∈ L.C i}

/-- The reference weight of one assignment: mesh, depth thickness, width and palette. -/
def weight (L : ProjLayer α) (N d s χ : ℝ) (π : Measure ℝ) (i : Fin L.n) : ENNReal :=
  ENNReal.ofReal (χ * (N ^ (-s)) ^ d * L.β) * π {w : ℝ | ⌊w / χ⌋ = L.tag i 0}

/-- Layer estimates at depth `s` with loss `H`, mesh `χ` and lower width exponent `La`.
The trajectory is that of the frozen model; every floor is charged to the original
residual `ρ`. -/
def Good (L : ProjLayer α) (N H d ell La s χ : ℝ) (b : α → Fin 6 → ℝ)
    (P : MvPolynomial (Fin 4) ℝ) (π : Measure ℝ) (ρ : Measure (α × ℝ)) : Prop :=
  0 < L.β ∧ N ^ (-ell * s) * N ^ (-La) / H ≤ L.β ∧ L.β ≤ H * N ^ (-ell * s) ∧
  (∀ i, MeasurableSet (L.C i)) ∧ (∀ i i', i ≠ i' → Disjoint (L.C i) (L.C i')) ∧
  ∀ i, |L.u i| + |L.v i| ≤ H ∧ (L.G i).totalDegree ≤ 2 ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ∀ w ∈ Icc (-1 : ℝ) 1,
      |eval ![t, L.u i + t * L.v i + L.β * w] (L.G i)| ≤ H) ∧
    (∀ l ∈ L.C i, ⌊b l 3 / χ⌋ = L.tag i 0 ∧ ⌊b l 0 / χ⌋ = L.tag i 1 ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        |(Submission.Lib.K4ContactNormalization.point (b l) t) 2 - L.u i - t * L.v i| ≤
          H * L.β ∧
        |eval (Submission.Lib.K4ContactNormalization.point (b l) t) P -
          eval ![t, (Submission.Lib.K4ContactNormalization.point (b l) t) 2] (L.G i)| ≤
          H * N ^ (-s)) ∧
    ENNReal.ofReal (χ * (N ^ (-s)) ^ d * L.β / H) * π {w : ℝ | ⌊w / χ⌋ = L.tag i 0} ≤
      ρ (L.C i ×ˢ Icc (0 : ℝ) 1)

/-- A larger loss supplies every weaker estimate. -/
theorem Good.mono {L : ProjLayer α} {N H H' d ell La s χ : ℝ} {b : α → Fin 6 → ℝ}
    {P : MvPolynomial (Fin 4) ℝ} {π : Measure ℝ} {ρ : Measure (α × ℝ)}
    (h : L.Good N H d ell La s χ b P π ρ) (hN : 0 < N) (hH : 0 < H) (hHH : H ≤ H')
    (hχ : 0 ≤ χ) : L.Good N H' d ell La s χ b P π ρ := by
  obtain ⟨hβ, hlow, hup, hmeas, hdisj, hi⟩ := h
  have hH' : 0 < H' := hH.trans_le hHH
  have hNs : 0 ≤ N ^ (-s) := Real.rpow_nonneg hN.le _
  refine ⟨hβ, ?_, ?_, hmeas, hdisj, ?_⟩
  · refine le_trans ?_ hlow
    apply div_le_div_of_nonneg_left _ hH hHH
    exact mul_nonneg (Real.rpow_nonneg hN.le _) (Real.rpow_nonneg hN.le _)
  · exact hup.trans (mul_le_mul_of_nonneg_right hHH (Real.rpow_nonneg hN.le _))
  · intro i
    obtain ⟨huv, hdeg, hnorm, hfit, hfloor⟩ := hi i
    refine ⟨huv.trans hHH, hdeg, fun t ht w hw => (hnorm t ht w hw).trans hHH, ?_, ?_⟩
    · intro l hl
      obtain ⟨h0, h1, ht⟩ := hfit l hl
      refine ⟨h0, h1, fun t htI => ⟨?_, ?_⟩⟩
      · exact (ht t htI).1.trans (mul_le_mul_of_nonneg_right hHH hβ.le)
      · exact (ht t htI).2.trans (mul_le_mul_of_nonneg_right hHH hNs)
    · refine le_trans ?_ hfloor
      gcongr

/-- The reference budget of a layer follows from its floors and disjointness. -/
theorem Good.weight_sum_le {L : ProjLayer α} {N H d ell La s χ : ℝ} {b : α → Fin 6 → ℝ}
    {P : MvPolynomial (Fin 4) ℝ} {π : Measure ℝ} {ρ : Measure (α × ℝ)}
    (h : L.Good N H d ell La s χ b P π ρ) (hH : 0 < H) :
    (∑ i, L.weight N d s χ π i) ≤ ENNReal.ofReal H * ρ univ := by
  obtain ⟨-, -, -, hmeas, hdisj, hi⟩ := h
  have hterm (i : Fin L.n) : L.weight N d s χ π i ≤
      ENNReal.ofReal H * ρ (L.C i ×ˢ Icc (0 : ℝ) 1) := by
    unfold weight
    have hsplit : ENNReal.ofReal (χ * (N ^ (-s)) ^ d * L.β) =
        ENNReal.ofReal H * ENNReal.ofReal (χ * (N ^ (-s)) ^ d * L.β / H) := by
      rw [← ENNReal.ofReal_mul hH.le]
      congr 1
      field_simp
    rw [hsplit, mul_assoc]
    exact mul_le_mul_right (hi i).2.2.2.2 _
  have hunion : (∑ i, ρ (L.C i ×ˢ Icc (0 : ℝ) 1)) = ρ (⋃ i, L.C i ×ˢ Icc (0 : ℝ) 1) := by
    rw [measure_iUnion, tsum_fintype]
    · intro i i' hii'
      exact Set.disjoint_prod.mpr (Or.inl (hdisj i i' hii'))
    · exact fun i => (hmeas i).prod measurableSet_Icc
  calc (∑ i, L.weight N d s χ π i)
      ≤ ∑ i, ENNReal.ofReal H * ρ (L.C i ×ˢ Icc (0 : ℝ) 1) := Finset.sum_le_sum fun i _ => hterm i
    _ = ENNReal.ofReal H * ρ (⋃ i, L.C i ×ˢ Icc (0 : ℝ) 1) := by
      rw [← Finset.mul_sum, hunion]
    _ ≤ ENNReal.ofReal H * ρ univ := by gcongr; exact subset_univ _

end ProjLayer

namespace PreparedModel

variable {α : Type} [MeasurableSpace α]

/-- The single-depth projection step at depth `s`, lower width exponent `La` and mesh
`χ = N^(-m)`, uniform over the dense submeasures of the original residual. -/
def SingleLayer (p : Parameters) (a : PreparedModel α) (s La m : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop,
    ∀ ζ : Measure (α × ℝ), ζ ≤ a.rho k → ENNReal.ofReal (p.N k ^ (-η)) ≤ ζ univ →
      ∃ (L : ProjLayer α) (ζ' : Measure (α × ℝ)), ζ' ≤ ζ ∧
        ENNReal.ofReal (p.N k ^ (-ε)) ≤ ζ' univ ∧ (∀ᵐ z ∂ζ', z ∈ L.covered) ∧
        L.Good (p.N k) (p.N k ^ ε) p.d p.ell La s (p.N k ^ (-m)) (a.b k) (a.P k)
          (a.pi k) (a.rho k)

/-- Ordinary projected preparation: single-depth steps at every depth in `[a, 2a]`
with `2a < U`, for every mesh exponent above `L a`, with one constant `L`. -/
def OrdinaryPreparation (p : Parameters) (a : PreparedModel α) : Prop :=
  ∃ L : ℝ, 2 < L ∧ ∀ a₀ : ℝ, 0 < a₀ → 2 * a₀ < p.U → ∀ s : ℝ, a₀ ≤ s → s ≤ 2 * a₀ →
    ∀ m : ℝ, L * a₀ < m → a.SingleLayer p s (L * a₀) m

/-- Successive selection at the depths of a finite set: every later selection is made
inside the previous dense residual, so all earlier coverages persist. -/
theorem finite_layers (p : Parameters) (a : PreparedModel α) (hN : ∀ k, 1 ≤ p.N k)
    (La m : ℝ) (D : Finset ℝ) (hstep : ∀ s ∈ D, a.SingleLayer p s La m) :
    ∀ ε : ℝ, 0 < ε → ∃ η : ℝ, 0 < η ∧ ∀ᶠ k in atTop,
      ∀ ζ₀ : Measure (α × ℝ), ζ₀ ≤ a.rho k → ENNReal.ofReal (p.N k ^ (-η)) ≤ ζ₀ univ →
        ∃ (L : ℝ → ProjLayer α) (ζ : Measure (α × ℝ)), ζ ≤ ζ₀ ∧
          ENNReal.ofReal (p.N k ^ (-ε)) ≤ ζ univ ∧
          (∀ s ∈ D, ∀ᵐ z ∂ζ, z ∈ (L s).covered) ∧
          ∀ s ∈ D, (L s).Good (p.N k) (p.N k ^ ε) p.d p.ell La s (p.N k ^ (-m)) (a.b k)
            (a.P k) (a.pi k) (a.rho k) := by
  classical
  induction D using Finset.induction_on with
  | empty =>
    intro ε hε
    refine ⟨ε, hε, Filter.Eventually.of_forall fun k ζ₀ _ hζ₀ => ?_⟩
    exact ⟨fun _ => ProjLayer.empty, ζ₀, le_rfl, hζ₀, by simp, by simp⟩
  | insert s₀ D hs₀ ih =>
    intro ε hε
    obtain ⟨ηD, hηD, HD⟩ := ih (fun s hs => hstep s (Finset.mem_insert_of_mem hs)) ε hε
    set ε₁ := min ε ηD with hε₁def
    have hε₁ : 0 < ε₁ := lt_min hε hηD
    obtain ⟨η₁, hη₁, H₁⟩ := hstep s₀ (Finset.mem_insert_self s₀ D) ε₁ hε₁
    refine ⟨η₁, hη₁, ?_⟩
    filter_upwards [H₁, HD] with k H₁ HD
    intro ζ₀ hζ₀ hm₀
    obtain ⟨L₀, ζ₁, hζ₁, hm₁, hc₁, hg₁⟩ := H₁ ζ₀ hζ₀ hm₀
    have hm₁' : ENNReal.ofReal (p.N k ^ (-ηD)) ≤ ζ₁ univ := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hm₁
      exact Real.rpow_le_rpow_of_exponent_le (hN k) (neg_le_neg (min_le_right _ _))
    obtain ⟨L, ζ, hζ, hm, hc, hg⟩ := HD ζ₁ (hζ₁.trans hζ₀) hm₁'
    have hNk : 0 < p.N k := lt_of_lt_of_le zero_lt_one (hN k)
    refine ⟨Function.update L s₀ L₀, ζ, hζ.trans hζ₁, hm, ?_, ?_⟩
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rw [Function.update_self]
        exact ae_mono hζ hc₁
      · have hne : s ≠ s₀ := fun h => hs₀ (h ▸ hs)
        rw [Function.update_of_ne hne]
        exact hc s hs
    · intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · rw [Function.update_self]
        exact hg₁.mono hNk (Real.rpow_pos_of_pos hNk _)
          (Real.rpow_le_rpow_of_exponent_le (hN k) (min_le_left _ _))
          (Real.rpow_nonneg hNk.le _)
      · have hne : s ≠ s₀ := fun h => hs₀ (h ▸ hs)
        rw [Function.update_of_ne hne]
        exact hg s hs

/-- A diagonal subsequence with one subpower loss carries simultaneous layers at all
depths of a finite set, on one common dense residual. -/
theorem exists_layers_of_single (p : Parameters) (hp : p.Valid) (a : PreparedModel α)
    (hcommon : a.Common p) (La m : ℝ) (D : Finset ℝ)
    (hstep : ∀ s ∈ D, a.SingleLayer p s La m) :
    ∃ τ : ℕ → ℕ, StrictMono τ ∧ ∃ H : ℕ → ℝ, (∀ k, 1 ≤ H k ∧ p.K (τ k) ≤ H k) ∧
      (∀ ε : ℝ, 0 < ε → ∀ᶠ k in atTop, H k ≤ p.N (τ k) ^ ε) ∧
      ∃ (ρ' : ℕ → Measure (α × ℝ)) (L : ℕ → ℝ → ProjLayer α),
        (∀ k, ρ' k ≤ a.rho (τ k) ∧ ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k univ) ∧
        ∀ k, ∀ s ∈ D,
          (L k s).Good (p.N (τ k)) (H k) p.d p.ell La s (p.N (τ k) ^ (-m)) (a.b (τ k))
            (a.P (τ k)) (a.pi (τ k)) (a.rho (τ k)) ∧
          (∑ i, (L k s).weight (p.N (τ k)) p.d s (p.N (τ k) ^ (-m)) (a.pi (τ k)) i) ≤
            ENNReal.ofReal (H k) ∧
          (∀ᵐ z ∂ρ' k, z ∈ (L k s).covered) := by
  classical
  obtain ⟨hN2, -, ⟨hK1, hKsub⟩, -⟩ := hp
  have hN : ∀ k, 1 ≤ p.N k := fun k => le_trans (by norm_num) (hN2 k)
  have hNpos : ∀ k, 0 < p.N k := fun k => lt_of_lt_of_le zero_lt_one (hN k)
  -- the losses `ε j = 1/(j+1)`
  let e : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have he : ∀ j, 0 < e j := fun j => by positivity
  have hsel : ∀ j, ∀ᶠ k in atTop, ∃ (L : ℝ → ProjLayer α) (ζ : Measure (α × ℝ)),
      ζ ≤ a.rho k ∧ ENNReal.ofReal (p.N k ^ (-e j)) ≤ ζ univ ∧
      (∀ s ∈ D, ∀ᵐ z ∂ζ, z ∈ (L s).covered) ∧
      ∀ s ∈ D, (L s).Good (p.N k) (p.N k ^ e j) p.d p.ell La s (p.N k ^ (-m)) (a.b k)
        (a.P k) (a.pi k) (a.rho k) := by
    intro j
    obtain ⟨η, hη, Hη⟩ := finite_layers p a hN La m D hstep (e j) (he j)
    filter_upwards [Hη, hKsub η hη] with k Hk hKk
    obtain ⟨L, ζ, hζ, hm, hc, hg⟩ := Hk (a.rho k) le_rfl (by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) (hcommon k).2.2.2.2.2.2.1
      rw [Real.rpow_neg (hNpos k).le]
      exact inv_anti₀ (lt_of_lt_of_le zero_lt_one (hK1 k)) hKk)
    exact ⟨L, ζ, hζ, hm, hc, hg⟩
  obtain ⟨τ, hτ, hτsel⟩ := Filter.extraction_forall_of_eventually hsel
  choose L ζ hζ hm hc hg using hτsel
  let H : ℕ → ℝ := fun j => p.K (τ j) * p.N (τ j) ^ e j
  have hpow1 : ∀ j, 1 ≤ p.N (τ j) ^ e j := fun j => Real.one_le_rpow (hN _) (he j).le
  have hHpow : ∀ j, p.N (τ j) ^ e j ≤ H j := fun j => le_mul_of_one_le_left
    (Real.rpow_nonneg (hNpos _).le _) (hK1 _)
  have hHK : ∀ j, p.K (τ j) ≤ H j := fun j => le_mul_of_one_le_right
    (le_trans zero_le_one (hK1 _)) (hpow1 j)
  have hHpos : ∀ j, 0 < H j := fun j => lt_of_lt_of_le one_pos ((hK1 _).trans (hHK j))
  refine ⟨τ, hτ, H, fun j => ⟨(hK1 _).trans (hHK j), hHK j⟩, ?_, ζ, L, ?_, ?_⟩
  · -- the loss is subpower along the subsequence
    intro ε hε
    have hKτ := hτ.tendsto_atTop.eventually (hKsub (ε / 2) (by positivity))
    have hsmall : ∀ᶠ j in atTop, e j ≤ ε / 2 := by
      obtain ⟨J, hJ⟩ := exists_nat_gt (2 / ε)
      filter_upwards [Filter.eventually_ge_atTop J] with j hj
      have hj' : (2 / ε) < (j : ℝ) + 1 := by
        have : (J : ℝ) ≤ j := by exact_mod_cast hj
        linarith
      show 1 / ((j : ℝ) + 1) ≤ ε / 2
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_lt_iff₀ hε] at hj'
      linarith
    filter_upwards [hKτ, hsmall] with j hKj hej
    calc H j = p.K (τ j) * p.N (τ j) ^ e j := rfl
      _ ≤ p.N (τ j) ^ (ε / 2) * p.N (τ j) ^ (ε / 2) := by
        apply mul_le_mul hKj (Real.rpow_le_rpow_of_exponent_le (hN _) hej)
          (Real.rpow_nonneg (hNpos _).le _) (Real.rpow_nonneg (hNpos _).le _)
      _ = p.N (τ j) ^ ε := by rw [← Real.rpow_add (hNpos _)]; ring_nf
  · intro j
    refine ⟨hζ j, le_trans (ENNReal.ofReal_le_ofReal ?_) (hm j)⟩
    rw [Real.rpow_neg (hNpos _).le]
    exact inv_anti₀ (Real.rpow_pos_of_pos (hNpos _) _) (hHpow j)
  · intro j s hs
    have hgs := hg j s hs
    refine ⟨hgs.mono (hNpos _) (Real.rpow_pos_of_pos (hNpos _) _) (hHpow j)
      (Real.rpow_nonneg (hNpos _).le _), ?_, hc j s hs⟩
    calc (∑ i, (L j s).weight (p.N (τ j)) p.d s (p.N (τ j) ^ (-m)) (a.pi (τ j)) i)
        ≤ ENNReal.ofReal (p.N (τ j) ^ e j) * a.rho (τ j) univ :=
          hgs.weight_sum_le (Real.rpow_pos_of_pos (hNpos _) _)
      _ ≤ ENNReal.ofReal (p.N (τ j) ^ e j) * ENNReal.ofReal (p.K (τ j)) := by
          gcongr; exact a.rho_univ_le p hcommon _
      _ = ENNReal.ofReal (H j) := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hNpos _).le _), mul_comm]

end PreparedModel

end

end Submission.Obl.k4_general_parent_projected_layers
