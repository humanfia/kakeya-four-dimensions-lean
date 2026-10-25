import Submission.Obl.k4_clean_cover_graph_atlas.Compatibility
import Submission.Obl.k4_clean_cover_graph_atlas.SampleInput

/-!
# Observation domains at one sample

The observation domains of the entry groups at one sample are the sets `groupObs` of
`Compatibility.lean`: terminal observations at which the group's old packet is canonically met,
whose base time lies in the group's sub-block and whose normalized position is within
`(κ + 1) 2^{-s₀}` of the group's box centre. From the sample input and the path alone:

* they are measurable (the path's charts give the old incidence sets a polynomial format);
* every covered incidence of an entry (an incidence of `V`, on a member line, in the entry's
  sub-block) observes inside its group's domain;
* one observation meets at most `⌈4 κ (2κ+3)²⌉ ≤ 101 κ³` groups of a world (the path's input lists
  have at most `κ` elements, and so have the canonical old lists).
-/

namespace Submission.Obl.k4_clean_cover_graph_atlas

open MeasureTheory Set Submission.Lib.K4XInterface

/-- A chart with any extra clause is a chart with the trivial extra clause. -/
theorem gchart_true {Nk : ℝ} {M D : ℕ} {κ : ℝ} {T : ℕ} {j r Bv : ℝ}
    {Ev : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {c u : EuclideanSpace ℝ (Fin 2)}
    {Q : Matrix (Fin 2) (Fin 2) ℝ} {R : MvPolynomial (Fin 4) ℝ} {A : Set (ℕ × (Fin 6 → ℝ))}
    {F : Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {ex : Prop}
    (h : gchart Nk M D κ T j r Bv Ev c u Q R A F ex) :
    gchart Nk M D κ T j r Bv Ev c u Q R A F True := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, -⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, trivial⟩

/-- The number of groups an observation meets, as a natural number, and its `κ³` bound. -/
theorem groupCount_bound {κ : ℝ} (hκ : 1 ≤ κ) :
    ((⌈4 * κ * (2 * κ + 3) ^ 2⌉₊ : ℕ) : ℝ) ≤ 101 * κ ^ 3 := by
  have h0 : 0 ≤ 4 * κ * (2 * κ + 3) ^ 2 := by positivity
  have h1 := Nat.ceil_lt_add_one h0
  have h2 : 4 * κ * (2 * κ + 3) ^ 2 ≤ 100 * κ ^ 3 := by
    have h3 : 2 * κ + 3 ≤ 5 * κ := by linarith
    have h4 : (2 * κ + 3) ^ 2 ≤ (5 * κ) ^ 2 := pow_le_pow_left₀ (by linarith) h3 2
    nlinarith
  have h5 : (1 : ℝ) ≤ κ ^ 3 := one_le_pow₀ hκ
  linarith

open Classical in
/-- **Observation domains of the groups at one sample.** -/
theorem sample_domains
    {Nk L : ℝ} {W : ℕ} {ω : Fin W → ℝ} {ν : Fin W → Measure (ℕ × (Fin 6 → ℝ))}
    {E : Fin W → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {B : Fin W → ℝ} {f : ℝ → ℝ} {Mpr Dpr : ℕ}
    {d₁ ρ gain δ₀ τ ε : ℝ} {m : ℕ} {r : ℕ → ℝ} {T : ℕ → ℕ} {C : ℕ}
    {lev : Fin C → ℕ} {γ : Fin C → Fin W} {j : Fin C → ℕ}
    {A : Fin C → Set (ℕ × (Fin 6 → ℝ))} {F : Fin C → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)}
    {Mg Dg : ℕ} {i : ℕ} {h : ℝ} {n : ℕ} {old : Fin n → Fin C}
    {R' : Fin n → MvPolynomial (Fin 4) ℝ} {A' : Fin n → Set (ℕ × (Fin 6 → ℝ))}
    {V : Fin n → Set ((ℕ × (Fin 6 → ℝ)) × ℝ)} {q : ℝ}
    {κ₁ : ℝ} {s : ℕ → ℝ} {Mp Dp : ℕ} {σ : ℝ} {nw : ℕ → ℝ} {κ : ℝ} {par : Fin C → Fin C}
    {c u : Fin C → EuclideanSpace ℝ (Fin 2)} {Q : Fin C → Matrix (Fin 2) (Fin 2) ℝ}
    {R : Fin C → MvPolynomial (Fin 4) ℝ}
    {lst : ℕ → Fin W → (EuclideanSpace ℝ (Fin 3) × ℤ) → Finset (Fin C)} {s₀ K : ℕ}
    (hNk : 1 ≤ Nk) (hgain : 0 ≤ gain)
    (hsi : SampleInput Nk L W ω ν E B f Mpr Dpr d₁ ρ gain δ₀ τ ε m r T C lev γ j A F Mg Dg
      i h n old R' A' V q)
    (hpath : path Nk L W ω ν E B f κ₁ m s δ₀ Mp Dp σ r T nw κ C lev par γ j c u Q R A F lst)
    (cov : Entry n s₀ K → Set ((ℕ × (Fin 6 → ℝ)) × ℝ))
    (hcov : ∀ e, ∀ p ∈ cov e, p ∈ V e.1 ∧ p.1 ∈ memE old R' A' j c u Q R (T i) s₀ K e ∧
      p.2 ∈ subBlock (T i) s₀ (j (old e.1)) e.2.1) :
    ∃ (S : Group C s₀ K → Set (EuclideanSpace ℝ (Fin 3) × ℤ)) (Dcount : ℕ),
      (∀ G, MeasurableSet (S G)) ∧
      (∀ e, ∀ p ∈ cov e, obs (B (γ (old e.1))) (δ Nk L) p ∈ S (entryGroup old e)) ∧
      (∀ w o, (Finset.univ.filter (fun G : Group C s₀ K => γ G.1 = w ∧ o ∈ S G)).card ≤ Dcount) ∧
      (Dcount : ℝ) ≤ 101 * κ ^ 3 := by
  classical
  obtain ⟨-, hi, hgh, -, -, hmargin, -, hentry, -, -, -, -, hq0, hqL, -, -⟩ := hsi
  have hκ : 1 ≤ κ := hpath.1
  have hlists : ∀ i' w o, ((lst i' w o).card : ℝ) ≤ κ := hpath.2.2.2.2.2.1
  have hcharts := hpath.2.2.2.2.2.2.2
  have hlevels := hpath.2.2.2.2.1
  -- the old incidence sets have a polynomial format
  have hfmtF : ∀ b q', fmt 7 (Nk ^ Mp) Dp
      {z : Fin 7 → ℝ | ((q', fun j' => z j'.castSucc), z 6) ∈ F b} := by
    intro b q'
    exact (((hcharts b).2.2).2.2.2.2.2.2.2.2.1 q').2
  -- the old charts of the entries, at the level `i`
  have hold : ∀ a, gchart Nk Mp Dp κ (T i) (j (old a) : ℝ) (r i) (B (γ (old a)))
      (E (γ (old a))) (c (old a)) (u (old a)) (Q (old a)) (R (old a)) (A (old a)) (F (old a))
      True := by
    intro a
    have hch := (hcharts (old a)).2.2
    rw [(hentry a).1] at hch
    exact gchart_true hch
  have hlev : ∀ a, lev (old a) = i := fun a => (hentry a).1
  have hA'A : ∀ a, A' a ⊆ A (old a) := fun a => (hentry a).2.2.2.2.2.1
  -- the canonical old lists have at most `κ` elements
  have hinput : ∀ b, ∀ p ∈ F b, b ∈ lst (lev b) (γ b) (obs (B (γ b)) (δ Nk (r (lev b))) p) := by
    intro b p hp
    exact ((hcharts b).2.2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 p hp
  have hri : 0 ≤ r i := (hlevels i hi).2.1.le
  have hL : 0 ≤ L := hq0.trans hqL
  have hh : 0 ≤ h := hgain.trans hgh
  have hriL : r i ≤ L := by nlinarith
  refine ⟨groupObs lev γ B F Nk L i j c u Q (T i) s₀ K κ, ⌈4 * κ * (2 * κ + 3) ^ 2⌉₊,
    fun G => measurableSet_groupObs lev γ B F hfmtF Nk L i j c u Q (T i) s₀ K κ G,
    fun e p hp => ?_, fun w o => ?_, groupCount_bound hκ⟩
  · obtain ⟨hpV, hpm, hpt⟩ := hcov e p hp
    have hpF : p ∈ F (old e.1) := ((hentry e.1).2.2.2.2.2.2.2.2.2.1 hpV).1
    exact obs_mem_groupObs (E := E) (R := R) (A := A) (rold := r i) (ex := fun _ => True)
      hold hlev hA'A e hpF hpm hpt
  · have hcanon := card_canonicalOldLists_le lev γ B F r lst hNk hinput i hri hriL
      (hlists i) w o
    have hc := card_groups_le lev γ B F Nk L i j c u Q (T i) s₀ K (by linarith) w o hcanon
    have hle := hc.trans (Nat.le_ceil _)
    exact_mod_cast hle

end Submission.Obl.k4_clean_cover_graph_atlas
