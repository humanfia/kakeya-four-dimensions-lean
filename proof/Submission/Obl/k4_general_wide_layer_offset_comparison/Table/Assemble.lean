import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.Counts
import Submission.Obl.k4_general_wide_layer_offset_comparison.ReferenceMultiplicity

/-!
# The compared table from pointwise good data

The realized entries of the good data, with the true-label menus of the
native forward lists, the realized fine choices and the canonical offsets,
form a `ComparisonTable`. Every count is paid by an explicit polynomial in
the intrinsic loss `H₀`, `K`, the witness factor and the native list size;
the reference budget is charged to the original fine short-domain menus.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace ProjectedLayer

variable {α : Type} [MeasurableSpace α]

/-- Validity of a projected layer only weakens when the loss grows. -/
theorem Valid.mono {L : ProjectedLayer α} {p : Parent α} {k : ℕ} {s m H H' : ℝ}
    (hL : L.Valid p k s m H) (hN : 0 < p.N k) (hH : 0 < H) (hHH : H ≤ H') :
    L.Valid p k s m H' := by
  rcases hL with ⟨hβ, hlo, hhi, hmeas, hdisj, hi, hbudget⟩
  have hH' : 0 < H' := hH.trans_le hHH
  refine ⟨hβ, (div_le_div_of_nonneg_left (by positivity) hH hHH).trans hlo,
    hhi.trans (mul_le_mul_of_nonneg_right hHH (by positivity)), hmeas, hdisj, ?_,
    hbudget.trans (ENNReal.ofReal_le_ofReal hHH)⟩
  intro i
  obtain ⟨huv, hdeg, hnorm, hfit, hfloor⟩ := hi i
  refine ⟨huv.trans hHH, hdeg, fun t ht w hw => (hnorm t ht w hw).trans hHH, ?_, ?_⟩
  · intro l hl
    obtain ⟨h0, h1, hf⟩ := hfit l hl
    exact ⟨h0, h1, fun t ht => ⟨(hf t ht).1.trans (mul_le_mul_of_nonneg_right hHH hβ.le),
      (hf t ht).2.trans (mul_le_mul_of_nonneg_right hHH (by positivity))⟩⟩
  · refine le_trans ?_ hfloor
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    exact div_le_div_of_nonneg_left (by positivity) hH hHH

end ProjectedLayer

namespace Parent
namespace GoodTableData

variable {α : Type} [MeasurableSpace α] {p : Parent α} {k : ℕ} {r u v m H₀ H : ℝ}
  (t : p.GoodTableData k r u v m H₀ H)

/-- Coarse choices of a true label and a major bin: the native forward lists
over the true short-domain menu. -/
def coarseChoices (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) : Finset (Fin (t.layers 0).count) :=
  (p.trueDomains k r m Q tag).biUnion (fun D => t.fwd Q (tag, D))

open scoped Classical in
/-- Fine choices of a true label and a coarse label: those realized together. -/
def fineChoices (c : Fin 2) (Q : Fin (p.n k r)) (i : Fin (t.layers 0).count) :
    Finset (Fin (t.layers c.succ).count) :=
  ((t.tuples c).filter (fun e => e.1 = Q ∧ e.2.1 = i)).image (fun e => e.2.2.1)

theorem mem_fineChoices {c : Fin 2} {Q : Fin (p.n k r)} {i : Fin (t.layers 0).count}
    {j : Fin (t.layers c.succ).count} (hj : j ∈ t.fineChoices c Q i) :
    ∃ ω ∈ t.good, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q) ∧
      ω.1 ∈ (t.layers 0).C i ∧ ω.1 ∈ (t.layers c.succ).C j := by
  classical
  simp only [fineChoices, Finset.mem_image, Finset.mem_filter] at hj
  obtain ⟨e, ⟨he, hQ, hi⟩, rfl⟩ := hj
  obtain ⟨ω, hω, hm⟩ := (t.mem_tuples_iff c e).mp he
  obtain ⟨h1, h2, h3, h4, -⟩ := hm
  rw [hQ] at h1 h2
  rw [hi] at h3
  exact ⟨ω, hω, h1, h2, h3, h4⟩

theorem idx_mem_fineChoices (c : Fin 2) (e : Fin (t.count c)) :
    (t.idx c e).2.2.1 ∈ t.fineChoices c (t.idx c e).1 (t.idx c e).2.1 := by
  classical
  simp only [fineChoices, Finset.mem_image, Finset.mem_filter]
  exact ⟨t.idx c e, ⟨t.idx_mem c e, rfl, rfl⟩, rfl⟩

theorem idx_coarse_mem (c : Fin 2) (e : Fin (t.count c)) :
    (t.idx c e).2.1 ∈ t.coarseChoices (t.idx c e).1 ((t.layers 0).tag (t.idx c e).2.1) := by
  obtain ⟨ω, hω, hm⟩ := t.idx_realized c e
  have hD := t.domain_mem_trueDomains c hω hm
  obtain ⟨hQ, hQt, hi, -, hcode⟩ := hm
  have hnat := (t.good_native ω hω _ _ hQ hQt hi).1
  rw [t.shortComparisonCode_eq hi, hcode] at hnat
  exact Finset.mem_biUnion.mpr ⟨_, hD, hnat⟩

theorem coarseChoices_card (Q : Fin (p.n k r)) (tag : Fin 2 → ℤ) (hKnat : 0 ≤ t.Knat) :
    ((t.coarseChoices Q tag).card : ℝ) ≤ (4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat := by
  calc
    ((t.coarseChoices Q tag).card : ℝ) ≤
        ∑ D ∈ p.trueDomains k r m Q tag, ((t.fwd Q (tag, D)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _D ∈ p.trueDomains k r m Q tag, t.Knat :=
      Finset.sum_le_sum (fun D _ => t.fwd_card Q (tag, D))
    _ = ((p.trueDomains k r m Q tag).card : ℝ) * t.Knat := by simp
    _ ≤ (4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat :=
      mul_le_mul_of_nonneg_right (p.card_trueDomains_le k r m Q tag (K_nonneg t)) hKnat

/-- The reverse count with its actual bound. -/
theorem reverse_count_le (c : Fin 2) (hH : 10 * p.K k ≤ H) (hH₀ : 1 ≤ H₀)
    (hgain : 0 ≤ (![u, v] : Fin 2 → ℝ) c) (hKnat : 0 ≤ t.Knat)
    (tag : Fin 2 → ℤ) (D : ℤ × ℤ × ℤ) (j : Fin (t.layers c.succ).count) :
    ((Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e : Fin (t.count c),
      (t.idx c e).1 = Q ∧ (t.layers 0).tag (t.idx c e).2.1 = tag ∧
        (t.idx c e).2.2.2 = D ∧ (t.idx c e).2.2.1 = j)).card : ℝ) ≤
      16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat := by
  classical
  set Qs := Finset.univ.filter (fun Q : Fin (p.n k r) => ∃ e : Fin (t.count c),
      (t.idx c e).1 = Q ∧ (t.layers 0).tag (t.idx c e).2.1 = tag ∧
        (t.idx c e).2.2.2 = D ∧ (t.idx c e).2.2.1 = j) with hQs
  have hB0 : 0 ≤ 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat := by
    have := t.δ_pos
    have : 0 ≤ 5 * H₀ := by linarith
    positivity
  rcases Qs.eq_empty_or_nonempty with hQe | ⟨Q₀, hQ₀⟩
  · rw [hQe]
    simpa using hB0
  obtain ⟨e₀, -, -, hD₀, hj₀⟩ := (Finset.mem_filter.mp hQ₀).2
  obtain ⟨ω₀, hω₀, hm₀⟩ := t.idx_realized c e₀
  let I := Finset.univ.filter (fun i : Fin (t.layers 0).count => ∃ e : Fin (t.count c),
      (t.idx c e).2.1 = i ∧ (t.layers 0).tag i = tag ∧
        (t.idx c e).2.2.2 = D ∧ (t.idx c e).2.2.1 = j)
  have hω₀j : ω₀.1 ∈ (t.layers c.succ).C j := by
    have h := hm₀.2.2.2.1
    rw [hj₀] at h
    exact h
  have hIcard : (I.card : ℝ) ≤ 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ := by
    apply t.reverse_coarse_count c hω₀ j hω₀j I _ hH hH₀ hgain
    intro i hi
    obtain ⟨e, hei, -, heD, hej⟩ := (Finset.mem_filter.mp hi).2
    obtain ⟨ω, hω, hm⟩ := t.idx_realized c e
    obtain ⟨hQ, hQt, hi', hj', hcode⟩ := hm
    refine ⟨ω, hω, (t.idx c e).1, hQ, hQt, ?_, ?_, ?_⟩
    · rw [← hei]; exact hi'
    · rw [← hej]; exact hj'
    · rw [hcode, heD, ← hD₀]
      exact hm₀.2.2.2.2.symm
  have hsub : Qs ⊆ I.biUnion (fun i => t.rev i (tag, D)) := by
    intro Q hQ
    obtain ⟨e, heQ, hetag, heD, hej⟩ := (Finset.mem_filter.mp hQ).2
    obtain ⟨ω, hω, hm⟩ := t.idx_realized c e
    obtain ⟨hQ', hQt', hi', -, hcode⟩ := hm
    refine Finset.mem_biUnion.mpr ⟨(t.idx c e).2.1, ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, rfl, hetag, heD, hej⟩
    · have hnat := (t.good_native ω hω _ _ hQ' hQt' hi').2
      rw [t.shortComparisonCode_eq hi', hcode, hetag, heD, heQ] at hnat
      exact hnat
  calc
    (Qs.card : ℝ) ≤ ((I.biUnion (fun i => t.rev i (tag, D))).card : ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ i ∈ I, ((t.rev i (tag, D)).card : ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ I, t.Knat := Finset.sum_le_sum (fun i _ => t.rev_card i (tag, D))
    _ = (I.card : ℝ) * t.Knat := by simp
    _ ≤ 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat :=
      mul_le_mul_of_nonneg_right hIcard hKnat

theorem gain_nonneg (hu : 0 ≤ u) (hv : 0 ≤ v) (c : Fin 2) :
    0 ≤ (![u, v] : Fin 2 → ℝ) c := by
  fin_cases c
  · exact hu
  · exact hv

/-- The fine scale ratio. -/
theorem scale_ratio (hN : 0 < p.N k) (c : Fin 2) (hd : 0 ≤ p.d) {X : ℝ} (hX : 0 ≤ X) :
    (X * p.N k ^ (-r) / p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d =
      X ^ p.d * p.N k ^ (p.d * (![u, v] : Fin 2 → ℝ) c) := by
  have hratio : p.N k ^ (-r) / p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c) =
      p.N k ^ ((![u, v] : Fin 2 → ℝ) c) := by
    rw [← Real.rpow_sub hN]
    congr 1
    ring
  rw [mul_div_assoc, hratio, Real.mul_rpow hX (Real.rpow_nonneg hN.le _),
    ← Real.rpow_mul hN.le, mul_comm ((![u, v] : Fin 2 → ℝ) c) p.d]

theorem entry_injective (c : Fin 2) :
    Function.Injective (fun e : Fin (t.count c) =>
      ((t.idx c e).1, (t.idx c e).2.1, (t.idx c e).2.2.1, (t.idx c e).2.2.2)) := by
  intro e f h
  simp only [Prod.mk.injEq] at h
  exact t.idx_injective c (Prod.ext h.1 (Prod.ext h.2.1 (Prod.ext h.2.2.1 h.2.2.2)))

theorem reference_budget_le (h10K : 10 * p.K k ≤ H) (hH₀ : 1 ≤ H₀) (hu : 0 ≤ u) (hv : 0 ≤ v)
    (hKnat : 0 ≤ t.Knat)
    (domains : ∀ c : Fin 2, Fin (t.layers c.succ).count → Finset (ℤ × ℤ × ℤ))
    (hdom : ∀ c j, ∀ l ∈ (t.layers c.succ).C j, ∀ s ∈ Icc (0 : ℝ) 1,
      movingDomainCode ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) (p.b k l 1) (p.b k l 4) s ∈
          domains c j)
    (R₀ : ℝ)
    (hbudget : ∀ c : Fin 2, (∑ j, ∑ D ∈ domains c j,
      ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
        (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
        (p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (t.layers c.succ).tag j 0}) ≤ ENNReal.ofReal R₀)
    (a : Fin 2) :
    (∑ e : Fin (t.count a), ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) a)) ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (t.layers 0).tag (t.idx a e).2.1 0}) ≤
      ENNReal.ofReal ((4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat *
        (16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat) * R₀) := by
    have hA : 0 ≤ (4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat := by
      have := K_nonneg t
      positivity
    have htags : ∀ e : Fin (t.count a), (t.layers 0).tag (t.idx a e).2.1 =
        (t.layers a.succ).tag (t.idx a e).2.2.1 := by
      intro e
      obtain ⟨ω, hω, hm⟩ := t.idx_realized a e
      exact t.tag_eq_of_mem hm.2.2.1 hm.2.2.2.1
    have hdom' : ∀ e : Fin (t.count a), (t.idx a e).2.2.2 ∈ domains a (t.idx a e).2.2.1 := by
      intro e
      obtain ⟨ω, hω, hm⟩ := t.idx_realized a e
      rw [← hm.2.2.2.2]
      exact hdom a _ ω.1 hm.2.2.2.1 ω.2 (t.good_base ω hω).1
    let w : Fin (t.layers a.succ).count → ℤ × ℤ × ℤ → ℝ≥0∞ := fun j _ =>
      ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
        (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
        (p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) a)) ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (t.layers a.succ).tag j 0}
    have hmain := compared_entry_reference_budget
      (fun e : Fin (t.count a) => (t.idx a e).1) (fun e => (t.idx a e).2.1)
      (fun e => (t.idx a e).2.2.1) (fun e => (t.idx a e).2.2.2)
      (t.layers 0).tag (t.layers a.succ).tag (t.entry_injective a) htags
      t.coarseChoices (fun e => t.idx_coarse_mem a e) hA
      (fun Q tag => t.coarseChoices_card Q tag hKnat)
      (B := 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat) (fun tag D j => by
        have h := t.reverse_count_le a h10K hH₀ (gain_nonneg hu hv a) hKnat tag D j
        convert h using 4)
      (domains a) hdom' w
    calc
      _ = ∑ e : Fin (t.count a), w (t.idx a e).2.2.1 (t.idx a e).2.2.2 := by
        apply Finset.sum_congr rfl
        intro e _
        simp only [w, htags e]
      _ ≤ _ := hmain
      _ ≤ ENNReal.ofReal ((4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat *
          (16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat)) * ENNReal.ofReal R₀ :=
        mul_le_mul' le_rfl (hbudget a)
      _ = _ := by
        rw [← ENNReal.ofReal_mul]
        have := t.δ_pos
        have : 0 ≤ 5 * H₀ := by linarith
        have := K_nonneg t
        positivity

/-- The compared table built from the realized entries of the good data. -/
def toTable (hH2 : 2 ≤ H) (hH₀ : 1 ≤ H₀) (hH₀H : H₀ ≤ H) (h3H₀ : 3 * H₀ ≤ H)
    (h10K : 10 * p.K k ≤ H) (hu : 0 ≤ u) (hv : 0 ≤ v) (hd : 0 ≤ p.d) (hKnat : 0 ≤ t.Knat)
    (hcoarse : (4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat ≤ H ^ 4)
    (hfine : ((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * t.δ⁻¹ *
      (2 * H₀ + 1) ^ p.d * (3 * H₀) ^ p.d ≤ H ^ 4)
    (hoff : ((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * t.δ⁻¹ *
      (2 * H₀ + 1) ^ p.d ≤ H ^ 10)
    (hrev : 16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat ≤ H ^ 4)
    (domains : ∀ c : Fin 2, Fin (t.layers c.succ).count → Finset (ℤ × ℤ × ℤ))
    (hdom : ∀ c j, ∀ l ∈ (t.layers c.succ).C j, ∀ s ∈ Icc (0 : ℝ) 1,
      movingDomainCode ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
        ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) (p.b k l 1) (p.b k l 4) s ∈
          domains c j)
    (R₀ : ℝ)
    (hbudget : ∀ c : Fin 2, (∑ j, ∑ D ∈ domains c j,
      ENNReal.ofReal (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
        (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
        (p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) c)) ^ p.d) *
        p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (t.layers c.succ).tag j 0}) ≤ ENNReal.ofReal R₀) :
    p.ComparisonTable k r u v m H
      ((4 * p.K k + 5) * (6 * p.K k + 5) * t.Knat *
        (16800 * p.K k ^ 2 * (5 * H₀) ^ p.d / t.δ * t.Knat) * R₀) where
  loss_one := hH2
  layers := t.layers
  layer_valid a := (t.layer_valid a).mono (N_pos t) (by linarith) hH₀H
  coefficient_bound := t.coefficient_bound
  law := t.law
  le_rho := t.le_rho
  count := t.count
  parent a e := (t.idx a e).1
  coarse a e := (t.idx a e).2.1
  fine a e := (t.idx a e).2.2.1
  domain a e := (t.idx a e).2.2.2
  event a e := t.entryEvent a (t.idx a e)
  event_measurable a e := t.measurableSet_entryEvent a _
  event_disjoint a := t.entryEvent_disjoint a
  event_cover a := t.entryEvent_cover a
  entry_injective a := t.entry_injective a
  event_data a e ω hω :=
    ⟨t.good_base ω hω.1, hω.2.1, hω.2.2.1, hω.2.2.2.1, hω.2.2.2.2.1, hω.2.2.2.2.2⟩
  palette_positive a e := by
    obtain ⟨ω, hω, hm⟩ := t.idx_realized a e
    have h := t.good_palette ω hω
    rwa [(t.label_tags hm.2.2.1).1] at h
  reference_budget a := t.reference_budget_le h10K hH₀ hu hv hKnat domains hdom R₀ hbudget a
  coarseChoices := t.coarseChoices
  coarse_card Q tag := (t.coarseChoices_card Q tag hKnat).trans hcoarse
  coarse_mem a e := t.idx_coarse_mem a e
  fineChoices := t.fineChoices
  fine_card a Q i := by
    classical
    have hN := N_pos t
    have hgain := gain_nonneg hu hv a
    have hac := t.fine_scale_le a hgain
    have hNr : 0 < p.N k ^ (-r) := Real.rpow_pos_of_pos hN _
    have hδ' : p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) a) ≤ 3 * H₀ * p.N k ^ (-r) :=
      hac.trans (le_mul_of_one_le_left hNr.le (by linarith))
    have hcount := t.fine_offset_count a Q i (t.fineChoices a Q i)
      (fun j hj => t.mem_fineChoices hj) h10K hH₀ 0 (3 * H₀ * p.N k ^ (-r)) hδ'
    have hall : (t.fineChoices a Q i).filter (fun j =>
        |p.canonicalOffset k r m (t.layers 0) (t.layers a.succ) Q i j - 0| ≤
          3 * H₀ * p.N k ^ (-r)) = t.fineChoices a Q i := by
      apply Finset.filter_true_of_mem
      intro j hj
      obtain ⟨ω, hω, hQ, hQt, hi, hj'⟩ := t.mem_fineChoices hj
      rw [sub_zero]
      exact t.offset_abs_le a hω hQ hQt hi hj' (by linarith) (by linarith) hH₀ hgain
    rw [hall] at hcount
    rw [scale_ratio hN a hd (by linarith : (0 : ℝ) ≤ 3 * H₀)] at hcount
    refine hcount.trans ?_
    have hNd : 0 ≤ p.N k ^ (p.d * (![u, v] : Fin 2 → ℝ) a) := Real.rpow_nonneg hN.le _
    calc
      ((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * t.δ⁻¹ *
          (2 * H₀ + 1) ^ p.d * ((3 * H₀) ^ p.d * p.N k ^ (p.d * (![u, v] : Fin 2 → ℝ) a)) =
        (((4 * p.K k + 5) * (6 * p.K k + 5) * (16800 * p.K k ^ 2)) * t.δ⁻¹ *
          (2 * H₀ + 1) ^ p.d * (3 * H₀) ^ p.d) *
          p.N k ^ (p.d * (![u, v] : Fin 2 → ℝ) a) := by ring
      _ ≤ H ^ 4 * p.N k ^ (p.d * (![u, v] : Fin 2 → ℝ) a) :=
        mul_le_mul_of_nonneg_right hfine hNd
  fine_mem a e := t.idx_mem_fineChoices a e
  offset a Q i j := p.canonicalOffset k r m (t.layers 0) (t.layers a.succ) Q i j
  offset_bound a Q i j hj := by
    obtain ⟨ω, hω, hQ, hQt, hi, hj'⟩ := t.mem_fineChoices hj
    have h := t.offset_abs_le a hω hQ hQt hi hj' (by linarith) (by linarith) hH₀
      (gain_nonneg hu hv a)
    exact h.trans (mul_le_mul_of_nonneg_right h3H₀ (Real.rpow_nonneg (N_pos t).le _))
  offset_fit a Q i j hj z hz := by
    obtain ⟨ω, hω, hQ, hQt, hi, hj'⟩ := t.mem_fineChoices hj
    have h := t.good_offset ω hω a Q i j hQ hQt hi hj' z hz
    exact h.trans (le_mul_of_one_le_left (Real.rpow_nonneg (N_pos t).le _) (by linarith))
  offset_count a Q i x δ hδ := by
    have hcount := t.fine_offset_count a Q i (t.fineChoices a Q i)
      (fun j hj => t.mem_fineChoices hj) h10K hH₀ x δ hδ
    refine hcount.trans ?_
    have hN := N_pos t
    have hδ0 : 0 ≤ δ / p.N k ^ (-r - (![u, v] : Fin 2 → ℝ) a) :=
      div_nonneg ((Real.rpow_nonneg hN.le _).trans hδ) (Real.rpow_nonneg hN.le _)
    exact mul_le_mul_of_nonneg_right hoff (Real.rpow_nonneg hδ0 _)
  reverse_count a tag D j :=
    (t.reverse_count_le a h10K hH₀ (gain_nonneg hu hv a) hKnat tag D j).trans hrev

end GoodTableData
end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
