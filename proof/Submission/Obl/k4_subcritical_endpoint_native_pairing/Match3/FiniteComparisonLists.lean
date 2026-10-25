/- Adapted from this LOT tree, obligation o218, session x0764, commit e1e41f8e737fdc1974cfdf32d18bbf69838b3ce8,
   Submission/Obl/k4_horizontal_endpoint_wide_return/Match3/FiniteComparisonLists.lean.
   Original source attributions are retained below. -/
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.GlobalComparison
import Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3.Lists
import Submission.Obl.k4_subcritical_endpoint_native_pairing.ComparisonLabels
import Submission.Obl.k4_subcritical_endpoint_native_pairing.ComparisonPruning

namespace Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3

open Set MeasureTheory

/-- Starting with the original finite entry families, impose both marginal
floors on one law, construct the measurable paired labels, and remove the
matching failures. Both losses are charged to the original reference budget. -/
theorem finite_comparison_with_lists (hM : Matching) {d : ℝ} (hd0 : 0 ≤ d) (hd1 : d < 1) :
    ∃ η : ℝ, 0 < η ∧ ∃ R₀ : ℝ, 1 ≤ R₀ ∧
    ∀ (Ω Γ ι₁ ι₂ : Type) [MeasurableSpace Ω]
      [MeasurableSpace Γ] [MeasurableSingletonClass Γ]
      [MeasurableSpace ι₁] [MeasurableSpace ι₂]
      [MeasurableSingletonClass ι₁] [MeasurableSingletonClass ι₂]
      (μ : Measure Ω) [IsFiniteMeasure μ] (s₁ : Finset ι₁) (s₂ : Finset ι₂)
      (E₁ : ι₁ → Set Ω) (E₂ : ι₂ → Set Ω)
      (domain₁ : ι₁ → Γ) (domain₂ : ι₂ → Γ) (reader : Ω → Γ)
      (T P Q X : Ω → ℝ) (h₁ : ι₁ → Fin 6 → ℝ) (h₂ : ι₂ → Fin 6 → ℝ)
      (t₀ p₀ q₀ V : Γ → ℝ) (τ D δ δm E A₀ A Mst : ℝ) (B : ENNReal),
      Measurable reader → Measurable T → Measurable P → Measurable Q →
      (∀ i, MeasurableSet (E₁ i)) → (∀ j, MeasurableSet (E₂ j)) →
      (∀ i ∈ s₁, E₁ i ⊆ {ω | reader ω = domain₁ i}) →
      (∀ j ∈ s₂, E₂ j ⊆ {ω | reader ω = domain₂ j}) →
      (∀ᵐ ω ∂μ, ∀ i ∈ s₁, ∀ j ∈ s₁, ω ∈ E₁ i → ω ∈ E₁ j → i = j) →
      (∀ᵐ ω ∂μ, ∀ i ∈ s₂, ∀ j ∈ s₂, ω ∈ E₂ i → ω ∈ E₂ j → i = j) →
      (∀ᵐ ω ∂μ, ∃ i ∈ s₁, ω ∈ E₁ i) → (∀ᵐ ω ∂μ, ∃ j ∈ s₂, ω ∈ E₂ j) →
      0 < τ → 0 < D → 0 < δ → δ ≤ 1 → 0 < δm → (∀ g, 0 < V g) → 1 ≤ E → 0 < A₀ →
      15360 * E * δm ≤ δ * τ → 15360 * E * δm ≤ δ * D →
      R₀ * δ ≤ Mst → 13720 ≤ A → 2000000 * A₀ * E ≤ A → A ≤ (Mst / δ) ^ η →
      (∀ g, ∀ᵐ ω ∂μ.restrict {ω | reader ω = g},
        T ω ∈ Icc (t₀ g) (t₀ g + τ) ∧ P ω ∈ Icc (p₀ g) (p₀ g + D) ∧
          Q ω ∈ Icc (q₀ g) (q₀ g + D)) →
      (∀ i ∈ s₁, ∀ ω ∈ E₁ i,
        |X ω - parameterPredictor (h₁ i) (T ω) (P ω) (Q ω)| ≤ δ / 2) →
      (∀ j ∈ s₂, ∀ ω ∈ E₂ j,
        |X ω - parameterPredictor (h₂ j) (T ω) (P ω) (Q ω)| ≤ δ / 2) →
      (∀ i ∈ s₁, ∀ t ∈ Icc (t₀ (domain₁ i)) (t₀ (domain₁ i) + τ),
        ∀ p ∈ Icc (p₀ (domain₁ i)) (p₀ (domain₁ i) + D),
        ∀ q ∈ Icc (q₀ (domain₁ i)) (q₀ (domain₁ i) + D),
          |parameterPredictor (h₁ i) t p q| ≤ E) →
      (∀ j ∈ s₂, ∀ t ∈ Icc (t₀ (domain₂ j)) (t₀ (domain₂ j) + τ),
        ∀ p ∈ Icc (p₀ (domain₂ j)) (p₀ (domain₂ j) + D),
        ∀ q ∈ Icc (q₀ (domain₂ j)) (q₀ (domain₂ j) + D),
          |parameterPredictor (h₂ j) t p q| ≤ E) →
      (∀ g σ, δ ≤ σ → σ ≤ 1 → ∀ (c : Fin 3 → ℤ) (j : ℤ),
        (μ.restrict {ω | reader ω = g})
          {ω | (fun k => ⌊(![T ω, P ω, Q ω] : Fin 3 → ℝ) k / δm⌋) = c ∧ ⌊X ω / σ⌋ = j} ≤
            ENNReal.ofReal (V g * σ ^ d * δm ^ 3)) →
      ((∑ i ∈ s₁, ENNReal.ofReal (τ * D ^ 2 * V (domain₁ i) * δ ^ d)) +
        (∑ j ∈ s₂, ENNReal.ofReal (τ * D ^ 2 * V (domain₂ j) * δ ^ d))) ≤ B →
      ENNReal.ofReal A₀⁻¹ * B < μ univ →
      ∃ ξ : Measure Ω, ξ ≤ μ ∧
        μ univ ≤ ξ univ +
          (ENNReal.ofReal A₀⁻¹ + ENNReal.ofReal (A * (Mst / δ) ^ (-η))) * B ∧
        ∃ L : ι₁ → Finset ι₂, (∀ i, L i ⊆ s₂) ∧
          (∀ i, ((L i).card : ℝ) ≤ 2000000 * A₀ * E * ((5120 * Mst) / δ) ^ d) ∧
          ∀ᵐ ω ∂ξ, ∃ i ∈ s₁, ∃ j ∈ s₂,
            ω ∈ E₁ i ∧ ω ∈ E₂ j ∧ domain₁ i = reader ω ∧ domain₂ j = reader ω ∧ j ∈ L i ∧
          ∀ t p q : ℝ, |t - (t₀ (reader ω) + τ / 2)| ≤ 4 * τ →
            |p - (p₀ (reader ω) + D / 2)| ≤ 4 * D →
            |q - (q₀ (reader ω) + D / 2)| ≤ 4 * D →
            |parameterPredictor (h₁ i) t p q - parameterPredictor (h₂ j) t p q| < 10 * Mst := by
  obtain ⟨η, hη, R₀, hR₀, H⟩ := global_comparison hM hd0 hd1
  refine ⟨η, hη, R₀, hR₀, ?_⟩
  intro Ω Γ ι₁ ι₂ _ _ _ _ _ _ _ μ _ s₁ s₂ E₁ E₂ domain₁ domain₂ reader T P Q X h₁ h₂
    t₀ p₀ q₀ V τ D δ δm E A₀ A Mst B hreader hT hP hQ hE₁ hE₂ hsub₁ hsub₂
    huniq₁ huniq₂ hcover₁ hcover₂ hτ hD hδ hδ1 hδm hV hE hA₀ hmτ hmD hMst hA1 hA2 hA
    hbox hfit₁ hfit₂ hnorm₁ hnorm₂ hcap hbudget hmass
  classical
  let ref : Γ → ENNReal := fun g => ENNReal.ofReal (τ * D ^ 2 * V g * δ ^ d)
  obtain ⟨ρ, S₁, S₂, hρ, hloss, hS₁, hS₂, hfloor₁, hfloor₂, hpair⟩ :=
    prune_comparison_lists μ s₁ s₂ E₁ E₂ hE₁ hE₂ domain₁ domain₂ reader ref
      (ENNReal.ofReal A₀⁻¹) B hbudget hsub₁ hsub₂ hcover₁ hcover₂
  have hρ0 : ρ ≠ 0 := by
    intro hzero
    have hle : μ univ ≤ ENNReal.ofReal A₀⁻¹ * B := by simpa [hzero] using hloss
    exact (not_lt_of_ge hle) hmass
  have hc₁ : ∀ᵐ ω ∂ρ, ∃ i ∈ S₁, ω ∈ E₁ i := by
    filter_upwards [hpair] with ω hp
    obtain ⟨i, hi, j, hj, hpi, hpj, hdi, hdj⟩ := hp
    exact ⟨i, hi, hpi⟩
  have hc₂ : ∀ᵐ ω ∂ρ, ∃ j ∈ S₂, ω ∈ E₂ j := by
    filter_upwards [hpair] with ω hp
    obtain ⟨i, hi, j, hj, hpi, hpj, hdi, hdj⟩ := hp
    exact ⟨j, hj, hpj⟩
  obtain ⟨G, r, hr, hrAE, hactive, hrfiber⟩ :=
    exists_common_active_domain_reader ρ hρ0 S₁ S₂ domain₁ domain₂ reader hreader (by
      filter_upwards [hpair] with ω hp
      obtain ⟨i, hi, j, hj, hpi, hpj, hdi, hdj⟩ := hp
      exact ⟨i, hi, j, hj, hdi, hdj⟩)
  let I₁ (g : G) := comparisonDomainEntries S₁ domain₁ (g : Γ)
  let I₂ (g : G) := comparisonDomainEntries S₂ domain₂ (g : Γ)
  have hlabels₁ (g : G) := exists_measurable_domain_entry_labels ρ S₁ domain₁ reader hreader E₁ hE₁
    (fun i hi => hsub₁ i (hS₁ hi)) (by
      filter_upwards [huniq₁.filter_mono (ae_mono hρ)] with ω hp i hi j hj hpi hpj
      exact hp i (hS₁ hi) j (hS₁ hj) hpi hpj) hc₁ (g : Γ) (hactive g).1
  have hlabels₂ (g : G) := exists_measurable_domain_entry_labels ρ S₂ domain₂ reader hreader E₂ hE₂
    (fun j hj => hsub₂ j (hS₂ hj)) (by
      filter_upwards [huniq₂.filter_mono (ae_mono hρ)] with ω hp i hi j hj hpi hpj
      exact hp i (hS₂ hi) j (hS₂ hj) hpi hpj) hc₂ (g : Γ) (hactive g).2
  choose f₁ hf₁ hmem₁ hmass₁ using hlabels₁
  choose f₂ hf₂ hmem₂ hmass₂ using hlabels₂
  have hentry₁ (g : G) (i : I₁ g) : (i : ι₁) ∈ S₁ ∧ domain₁ i = (g : Γ) :=
    (mem_comparisonDomainEntries _ _ _ _).mp i.property
  have hentry₂ (g : G) (j : I₂ g) : (j : ι₂) ∈ S₂ ∧ domain₂ j = (g : Γ) :=
    (mem_comparisonDomainEntries _ _ _ _).mp j.property
  have hscale (g : G) : ENNReal.ofReal (τ * D ^ 2 * V g * δ ^ d / A₀) =
      ENNReal.ofReal A₀⁻¹ * ref g := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hA₀.le)]
    congr 1
    ring
  have hnewbudget :
      (∑ g : G, ENNReal.ofReal (((Fintype.card (I₁ g) + Fintype.card (I₂ g) : ℕ) : ℝ) *
        (τ * D ^ 2 * V g * δ ^ d))) ≤ B := by
    calc
      _ = (∑ g ∈ G, ((comparisonDomainEntries S₁ domain₁ g).card : ENNReal) * ref g) +
          (∑ g ∈ G, ((comparisonDomainEntries S₂ domain₂ g).card : ENNReal) * ref g) := by
        have hterm (g : G) :
            ENNReal.ofReal (((Fintype.card (I₁ g) + Fintype.card (I₂ g) : ℕ) : ℝ) *
              (τ * D ^ 2 * V g * δ ^ d)) =
            ((comparisonDomainEntries S₁ domain₁ (g : Γ)).card : ENNReal) * ref g +
              ((comparisonDomainEntries S₂ domain₂ (g : Γ)).card : ENNReal) * ref g := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          simp only [I₁, I₂, Fintype.card_coe, Nat.cast_add, add_mul, ref]
        simp_rw [hterm]
        rw [Finset.sum_add_distrib]
        exact congrArg₂ (fun x y : ENNReal => x + y)
          (Finset.sum_coe_sort G (fun g => ((comparisonDomainEntries S₁ domain₁ g).card : ENNReal) * ref g))
          (Finset.sum_coe_sort G (fun g => ((comparisonDomainEntries S₂ domain₂ g).card : ENNReal) * ref g))
      _ ≤ (∑ i ∈ S₁, ref (domain₁ i)) + (∑ j ∈ S₂, ref (domain₂ j)) :=
        add_le_add (comparison_domain_reference_budget S₁ domain₁ G ref)
          (comparison_domain_reference_budget S₂ domain₂ G ref)
      _ ≤ (∑ i ∈ s₁, ref (domain₁ i)) + (∑ j ∈ s₂, ref (domain₂ j)) :=
        add_le_add (Finset.sum_le_sum_of_subset hS₁) (Finset.sum_le_sum_of_subset hS₂)
      _ ≤ B := hbudget
  have hδMst : δ ≤ Mst := by nlinarith
  have hMstpos : 0 < Mst := hδ.trans_le hδMst
  let nativeList (g : G) (i : ι₁) : Finset (I₂ g) :=
    parameterComparisonList (fun j => h₂ j) (h₁ i) (t₀ g) τ (p₀ g) (q₀ g) D (10 * Mst)
  have hlistCard (g : G) (i : ι₁) : ((nativeList g i).card : ℝ) ≤
      2000000 * A₀ * E * ((5120 * Mst) / δ) ^ d := by
    have hcount := parameter_comparison_list_count (ρ.restrict {ω | reader ω = (g : Γ)})
      (f₂ g) T P Q X (fun j : I₂ g => h₂ j) (h₁ i)
      (hf₂ g) hτ hD hδ hδ1 hδm (hV g) hE hA₀ hd0 hd1 hmτ hmD
      (by
        filter_upwards [(hbox g).filter_mono (ae_mono (Measure.restrict_mono_measure hρ _)),
          hmem₂ g] with ω hboxω hpj
        exact ⟨hboxω.1, hboxω.2.1, hboxω.2.2,
          hfit₂ _ (hS₂ (hentry₂ g (f₂ g ω)).1) ω hpj⟩)
      (fun j => by
        have hj := hnorm₂ j (hS₂ (hentry₂ g j).1)
        rw [(hentry₂ g j).2] at hj
        exact hj)
      (fun j => by
        rw [hmass₂ g j, hscale g]
        simpa only [(hentry₂ g j).2] using hfloor₂ j (hentry₂ g j).1)
      (fun σ hσ hσ1 c j =>
        (Measure.restrict_mono_measure hρ _ _).trans (hcap g σ hσ hσ1 c j))
      (M := 10 * Mst) (by linarith)
    simpa only [nativeList, show 512 * (10 * Mst) = 5120 * Mst by ring] using hcount
  let L (i : ι₁) : Finset ι₂ := if hg : domain₁ i ∈ G then
    (nativeList ⟨domain₁ i, hg⟩ i).image Subtype.val else ∅
  have hLdef (g : G) (i : ι₁) (hdi : domain₁ i = (g : Γ)) :
      L i = (nativeList g i).image Subtype.val := by
    have hg : domain₁ i ∈ G := hdi ▸ g.property
    have heq : (⟨domain₁ i, hg⟩ : G) = g := Subtype.ext hdi
    simp only [L, dif_pos hg]
    exact congrArg (fun a : G => (nativeList a i).image Subtype.val) heq
  have hLsub (i : ι₁) : L i ⊆ s₂ := by
    dsimp only [L]
    split_ifs with hg
    · intro j hj
      obtain ⟨j', hj', rfl⟩ := Finset.mem_image.mp hj
      exact hS₂ (hentry₂ ⟨domain₁ i, hg⟩ j').1
    · exact Finset.empty_subset _
  have hLcard (i : ι₁) : ((L i).card : ℝ) ≤
      2000000 * A₀ * E * ((5120 * Mst) / δ) ^ d := by
    dsimp only [L]
    split_ifs with hg
    · exact (show (((nativeList ⟨domain₁ i, hg⟩ i).image Subtype.val).card : ℝ) ≤
          ((nativeList ⟨domain₁ i, hg⟩ i).card : ℝ) by exact_mod_cast Finset.card_image_le).trans
        (hlistCard ⟨domain₁ i, hg⟩ i)
    · simp only [Finset.card_empty, Nat.cast_zero]
      positivity
  have : IsFiniteMeasure ρ := isFiniteMeasure_of_le μ hρ
  obtain ⟨ξ, hξ, hξloss, hgood⟩ := H Ω ρ G (fun g => I₁ g) (fun g => I₂ g) r f₁ f₂
    T P Q X (fun g i => h₁ i) (fun g j => h₂ j)
    (fun g => t₀ g) (fun g => p₀ g) (fun g => q₀ g) (fun g => V g)
    τ D δ δm E A₀ A Mst B hr hf₁ hf₂ hT hP hQ hτ hD hδ hδ1 hδm (fun g => hV g)
    hE hA₀ hmτ hmD hMst hA1 hA2 hA
    (fun g => by
      change ∀ᵐ ω ∂ρ.restrict {ω | r ω = g}, _
      rw [hrfiber g]
      filter_upwards [(hbox g).filter_mono (ae_mono (Measure.restrict_mono_measure hρ _)),
        hmem₁ g, hmem₂ g] with ω hboxω hpi hpj
      exact ⟨hboxω.1, hboxω.2.1, hboxω.2.2,
        hfit₁ _ (hS₁ (hentry₁ g (f₁ g ω)).1) ω hpi,
        hfit₂ _ (hS₂ (hentry₂ g (f₂ g ω)).1) ω hpj⟩)
    (fun g i => by
      have hi := hnorm₁ i (hS₁ (hentry₁ g i).1)
      rw [(hentry₁ g i).2] at hi
      exact hi)
    (fun g j => by
      have hj := hnorm₂ j (hS₂ (hentry₂ g j).1)
      rw [(hentry₂ g j).2] at hj
      exact hj)
    (fun g i => by
      change _ ≤ (ρ.restrict {ω | r ω = g}) _
      rw [hrfiber g, hmass₁ g i, hscale g]
      simpa only [(hentry₁ g i).2] using hfloor₁ i (hentry₁ g i).1)
    (fun g j => by
      change _ ≤ (ρ.restrict {ω | r ω = g}) _
      rw [hrfiber g, hmass₂ g j, hscale g]
      simpa only [(hentry₂ g j).2] using hfloor₂ j (hentry₂ g j).1)
    (fun g σ hσ hσ1 c j => by
      change (ρ.restrict {ω | r ω = g}) _ ≤ _
      rw [hrfiber g]
      exact (Measure.restrict_mono_measure hρ _ _).trans (hcap g σ hσ hσ1 c j)) hnewbudget
  have hsel : ∀ᵐ ω ∂ρ, ∀ g : G, r ω = g → ω ∈ E₁ (f₁ g ω) ∧ ω ∈ E₂ (f₂ g ω) := by
    rw [ae_all_iff]
    intro g
    apply (ae_restrict_iff' (hr (measurableSet_singleton g))).mp
    change ∀ᵐ ω ∂ρ.restrict {ω | r ω = g}, ω ∈ E₁ (f₁ g ω) ∧ ω ∈ E₂ (f₂ g ω)
    rw [hrfiber g]
    exact (hmem₁ g).and (hmem₂ g)
  refine ⟨ξ, hξ.trans hρ, hloss.trans ?_, L, hLsub, hLcard, ?_⟩
  · calc
      ρ univ + ENNReal.ofReal A₀⁻¹ * B ≤
          (ξ univ + ENNReal.ofReal (A * (Mst / δ) ^ (-η)) * B) + ENNReal.ofReal A₀⁻¹ * B :=
        add_le_add hξloss le_rfl
      _ = _ := by ring
  · filter_upwards [hsel.filter_mono (ae_mono hξ), hrAE.filter_mono (ae_mono hξ), hgood]
      with ω hselω hrω hgoodω
    let g := r ω
    let i := f₁ g ω
    let j := f₂ g ω
    obtain ⟨hpi, hpj⟩ := hselω g rfl
    have hcomparison : ∀ t p q : ℝ, |t - (t₀ g + τ / 2)| ≤ 4 * τ →
        |p - (p₀ g + D / 2)| ≤ 4 * D → |q - (q₀ g + D / 2)| ≤ 4 * D →
        |parameterPredictor (h₁ i) t p q - parameterPredictor (h₂ j) t p q| < 10 * Mst := by
      intro t p q ht hp hq
      apply lt_of_not_ge
      intro hlarge
      exact hgoodω ⟨t, p, q, ht, hp, hq, hlarge⟩
    have henlarge {x a w : ℝ} (hw : 0 < w) (hx : x ∈ Icc a (a + w)) :
        |x - (a + w / 2)| ≤ 4 * w := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2]
    have hjList : (j : ι₂) ∈ L i := by
      rw [hLdef g i (hentry₁ g i).2]
      apply Finset.mem_image.mpr
      refine ⟨j, (mem_parameterComparisonList _ _ _ _ _ _ _ _ _).mpr ?_, rfl⟩
      intro t ht p hp q hq
      simpa only [abs_sub_comm] using
        (hcomparison t p q (henlarge hτ ht) (henlarge hD hp) (henlarge hD hq)).le
    refine ⟨i, hS₁ (hentry₁ g i).1, j, hS₂ (hentry₂ g j).1, hpi, hpj,
      (hentry₁ g i).2.trans hrω, (hentry₂ g j).2.trans hrω, hjList, ?_⟩
    intro t p q ht hp hq
    exact hcomparison t p q (by simpa only [g, hrω] using ht) (by simpa only [g, hrω] using hp)
      (by simpa only [g, hrω] using hq)
end Submission.Obl.k4_subcritical_endpoint_native_pairing.Match3
