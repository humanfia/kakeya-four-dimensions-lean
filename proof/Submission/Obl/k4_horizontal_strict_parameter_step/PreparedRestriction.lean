/- Adapted from this LOT tree, obligation o245, session x0928,
branch x0928 at 9c7454a86c55309bdc5fec531b33288808d4b082, file `Submission/Obl/k4_horizontal_interior_parameter_bootstrap/PreparedRestriction.lean`.
Namespace and internal imports changed to o272; earlier provenance is retained. -/
import Submission.Obl.k4_horizontal_strict_parameter_step.Interface

namespace Submission.Obl.k4_horizontal_strict_parameter_step

open MeasureTheory Filter

/-- The geometric and reference-law part of a prepared input survives a dense
restriction of the current law, after enlarging the common loss factor. -/
theorem Hyp1.restrictCurrent {K H : ℕ → ℝ} {α : Type} [MeasurableSpace α]
    {ν : ℕ → Measure α} {μ ρ ρ' : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ}
    {b : ℕ → α → Fin 6 → ℝ} {P : ℕ → MvPolynomial (Fin 4) ℝ}
    (h : Hyp1 K ν μ ρ π b P) (hK : ∀ k, 0 < K k) (hKH : ∀ k, K k ≤ H k)
    (hρ : ∀ k, ρ' k ≤ ρ k) (hmass : ∀ k, ENNReal.ofReal ((H k)⁻¹) ≤ ρ' k Set.univ) :
    Hyp1 H ν μ ρ' π b P := by
  intro k
  obtain ⟨hbm, hν, hπ, hμ, hρμ, hsupp, -, hP, hbae, hpae⟩ := h k
  have hinv : (H k)⁻¹ ≤ (K k)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (hK k) (hKH k)
  refine ⟨hbm, hν, hπ, hμ.trans ?_, (hρ k).trans hρμ, hsupp, hmass k, hP,
    hbae.mono (fun l hl => hl.trans (hKH k)), ?_⟩
  · intro E
    change ENNReal.ofReal (K k) * (ν k).prod volume E ≤
      ENNReal.ofReal (H k) * (ν k).prod volume E
    gcongr
    exact hKH k
  · filter_upwards [hpae] with p hp
    refine ⟨?_, hinv.trans hp.2⟩
    intro t ht
    exact ⟨(hp.1 t ht).1.trans (hKH k), (hp.1 t ht).2.1.trans (hKH k),
      (hp.1 t ht).2.2.trans (hKH k)⟩

/-- Pure and joint caps use the original incidence law, and persist when their
common loss factor is enlarged. -/
theorem Hyp2.monoK {N K H : ℕ → ℝ} {d S : ℝ} {α : Type} [MeasurableSpace α]
    {μ : ℕ → Measure (α × ℝ)} {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ}
    {P : ℕ → MvPolynomial (Fin 4) ℝ} (h : Hyp2 N K d S μ π b P)
    (hN : ∀ k, 0 ≤ N k) (hKH : ∀ k, K k ≤ H k) : Hyp2 N H d S μ π b P := by
  intro R hR
  filter_upwards [h R hR] with k hk
  intro r s v hr hrR hs hsR hv hvR
  obtain ⟨hπ, hpure, hjoint⟩ := hk r s v hr hrR hs hsR hv hvR
  refine ⟨?_, ?_, ?_⟩
  · intro j
    refine (hπ j).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (hKH k) (Real.rpow_nonneg (hN k) _)
  · intro h q j
    refine (hpure h q j).trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (hKH k) (Real.rpow_nonneg (hN k) _)
  · intro h q j v₀
    refine (hjoint h q j v₀).trans ?_
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (hKH k) (Real.rpow_nonneg (hN k) _))) zero_le

/-- Native true assignments, their original priors, and earlier fit witnesses are
unchanged when the loss factor is enlarged for a dense current restriction. -/
theorem Hyp3.monoK {N K H : ℕ → ℝ} {d κ ℓ U e₀ : ℝ} {α : Type}
    [MeasurableSpace α] {ν : ℕ → Measure α} {μ : ℕ → Measure (α × ℝ)}
    {π : ℕ → Measure ℝ} {b : ℕ → α → Fin 6 → ℝ} {P : ℕ → MvPolynomial (Fin 4) ℝ}
    {T n : ℕ → ℝ → ℕ}
    {j : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin (2 ^ T k s)}
    {A B : (k : ℕ) → (s : ℝ) → Fin (n k s) → Set α}
    {c : (k : ℕ) → (s : ℝ) → Fin (n k s) → Fin 5 → ℝ}
    {F : (k : ℕ) → (s : ℝ) → Fin (n k s) → MvPolynomial (Fin 4) ℝ}
    (h : Hyp3 N K d κ ℓ U e₀ ν μ π b P T n j A B c F)
    (hN : ∀ k, 0 < N k) (hK : ∀ k, 0 < K k) (hKH : ∀ k, K k ≤ H k) :
    Hyp3 N H d κ ℓ U e₀ ν μ π b P T n j A B c F := by
  intro R hR
  filter_upwards [h R hR] with k hk
  intro s hs hsU
  have hNk : 0 < N k := hN k
  have hKk : 0 < K k := hK k
  have hHk : 0 < H k := hKk.trans_le (hKH k)
  have hks := hk s hs hsU
  generalize hqdef : (2 : ℝ) ^ (-(T k s : ℤ)) = q at hks ⊢
  generalize hadef : N k ^ (-s) = a at hks ⊢
  generalize hgdef : N k ^ (-ℓ * s) = g at hks ⊢
  have hq : 0 < q := by rw [← hqdef]; positivity
  have ha : 0 < a := by rw [← hadef]; exact Real.rpow_pos_of_pos (hN k) _
  have hg : 0 < g := by rw [← hgdef]; exact Real.rpow_pos_of_pos (hN k) _
  obtain ⟨hTlo, hThi, hsets, hdisj, hentry, hcover, hpal⟩ := hks
  refine ⟨?_, ?_, hsets, hdisj, ?_, hcover, ?_⟩
  · exact (div_le_div_of_nonneg_left (Real.rpow_nonneg (hN k).le _) (hK k) (hKH k)).trans hTlo
  · exact hThi.trans (mul_le_mul_of_nonneg_right (hKH k) (Real.rpow_nonneg (hN k).le _))
  · intro i
    obtain ⟨hνlo, hνhi, hμlo, hc, hdeg, hpos, hfit, hder, hhor⟩ := hentry i
    refine ⟨?_, ?_, ?_, (fun e => (hc e).trans (hKH k)), hdeg, ?_, ?_, ?_, ?_⟩
    · exact (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_left (by positivity) (hK k) (hKH k))).trans hνlo
    · refine hνhi.trans (ENNReal.ofReal_le_ofReal ?_)
      gcongr
      exact hKH k
    · refine le_trans ?_ hμlo
      gcongr
      exact hKH k
    · intro l hl t ht
      obtain ⟨h1, h2, h3⟩ := hpos l hl t ht
      refine ⟨h1.trans ?_, h2.trans ?_, h3.trans ?_⟩ <;> gcongr <;> exact hKH k
    · intro l hl t ht
      obtain ⟨h1, h2, h3⟩ := hfit l hl t ht
      refine ⟨h1.trans ?_, h2.trans (hKH k), h3.trans ?_⟩
      · gcongr
        exact hKH k
      · exact div_le_div_of_nonneg_right (hKH k) ha.le
    · filter_upwards [hder] with p hp
      intro hl ht
      apply le_trans _ (hp hl ht)
      simpa only [one_div] using one_div_le_one_div_of_le (hK k) (hKH k)
    · intro htrue
      obtain ⟨hP, hcontact, hgeom, L, hFeq, hL, hgrad⟩ := hhor htrue
      refine ⟨hP, hcontact, hgeom.trans ?_, L, hFeq, hL.trans ?_, ?_⟩
      · gcongr
        exact hKH k
      · gcongr
        exact hKH k
      · intro l hl t ht
        refine (hgrad l hl t ht).trans ?_
        gcongr
        exact hKH k
  · intro i v v₀ hv hvR
    refine (hpal i v v₀ hv hvR).trans ?_
    gcongr
    exact hKH k

end Submission.Obl.k4_horizontal_strict_parameter_step
