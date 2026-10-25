import Submission.Obl.k4_general_wide_layer_offset_comparison.Table.TrueDomains
import Submission.Obl.k4_general_wide_layer_offset_comparison.ShortDomainFiber
import Submission.Obl.k4_general_wide_layer_offset_comparison.SampleAssembly

/-!
# Pointwise good data for one compared table

At one index `k` we collect, on a measurable set `good` carrying the whole
current law, every pointwise property that the compared table needs:
unique true labels, projected labels, positive palette bins, whole-fiber
offsets of the projected comparison, stored original witnesses of every
projected (label, short code) entry, and native true/coarse partner lists.

The events of the table are the `good` points sorted by their entry
`(true label, coarse label, fine label, short domain code)`.
-/

namespace Submission.Obl.k4_general_wide_layer_offset_comparison

open MeasureTheory Set MvPolynomial
open scoped ENNReal

noncomputable section

namespace Parent

variable {α : Type} [MeasurableSpace α] (p : Parent α)

/-- The four coordinates of a compared entry. -/
abbrev EntryTuple (k : ℕ) (r : ℝ) (A F : ProjectedLayer α) :=
  Fin (p.n k r) × Fin A.count × Fin F.count × (ℤ × ℤ × ℤ)

/-- The exact short domain code used by the frozen statement. -/
def shortDomainCode (k : ℕ) (r : ℝ) (ω : α × ℝ) : ℤ × ℤ × ℤ :=
  p.domainCode k ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
    ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) ω

theorem measurable_shortDomainCode (hbase : p.Basic) (k : ℕ) (r : ℝ) :
    Measurable (p.shortDomainCode k r) :=
  p.measurable_domainCode hbase k _ _ _

/-- A point realizes an entry. -/
def EntryMatches (k : ℕ) (r : ℝ) (A F : ProjectedLayer α)
    (e : p.EntryTuple k r A F) (ω : α × ℝ) : Prop :=
  ω.1 ∈ p.B k r e.1 ∧ ω.2 ∈ block (p.T k r) (p.j k r e.1) ∧ ω.1 ∈ A.C e.2.1 ∧
    ω.1 ∈ F.C e.2.2.1 ∧ p.shortDomainCode k r ω = e.2.2.2

/-- The canonical constant offset, read at the left endpoint of the true
block on the central line of the true fiber. -/
def canonicalOffset (k : ℕ) (r m : ℝ) (A F : ProjectedLayer α) (Q : Fin (p.n k r))
    (i : Fin A.count) (j : Fin F.count) : ℝ :=
  eval ![p.trueFiberPoint k r m Q (A.tag i) (((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ (p.T k r)) 0,
      p.trueFiberPoint k r m Q (A.tag i) (((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ (p.T k r)) 2]
      (F.G j) -
    eval ![p.trueFiberPoint k r m Q (A.tag i) (((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ (p.T k r)) 0,
      p.trueFiberPoint k r m Q (A.tag i) (((p.j k r Q : ℕ) : ℝ) / (2 : ℝ) ^ (p.T k r)) 2]
      (A.G i)

/-- The stored original witness of a projected entry on one short code. -/
def witnessSet (k : ℕ) (r : ℝ) (L : ProjectedLayer α) (i : Fin L.count)
    (D : ℤ × ℤ × ℤ) : Set (α × ℝ) :=
  {ω | ω ∈ p.baseGood k ∧ ω.1 ∈ L.C i ∧ p.shortDomainCode k r ω = D}

/-- All pointwise inputs of one compared table at index `k`.
`H₀` is the intrinsic loss of the layers and `Hf` the radius of the true
fiber boxes on which offsets are certified. -/
structure GoodTableData (k : ℕ) (r u v m H₀ Hf : ℝ) where
  basic : p.Basic
  N_one : 1 < p.N k
  K_one : 1 ≤ p.K k
  chi_width : p.N k ^ (-m) ≤ (2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)
  chi_slope : p.N k ^ (-m) ≤ p.N k ^ (-p.ℓ * r)
  R : ℝ
  atDepth : p.AtDepth k r R
  layers : Fin 3 → ProjectedLayer α
  layer_valid : ∀ a, (layers a).Valid p k (![r, r + u, r + v] a) m H₀
  coefficient_bound : ∀ a i e, |((layers a).G i).coeff e| ≤ p.N k ^ (m / 1000)
  law : Measure (α × ℝ)
  le_rho : law ≤ p.ρ k
  good : Set (α × ℝ)
  good_measurable : MeasurableSet good
  law_good : law goodᶜ = 0
  good_base : ∀ ω ∈ good, ω ∈ p.baseGood k
  good_true : ∀ ω ∈ good, ∃ Q, ω.1 ∈ p.B k r Q ∧ ω.2 ∈ block (p.T k r) (p.j k r Q)
  good_time : ∀ ω ∈ good, ∀ Q, ω.2 ∈ block (p.T k r) (p.j k r Q) →
    ⌊ω.2 / (2 : ℝ) ^ (-(p.T k r : ℤ))⌋ = ((p.j k r Q : ℕ) : ℤ)
  good_label : ∀ ω ∈ good, ∀ a, ∃ i, ω.1 ∈ (layers a).C i
  good_palette : ∀ ω ∈ good,
    0 < p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋}
  good_offset : ∀ ω ∈ good, ∀ (c : Fin 2) (Q : Fin (p.n k r))
      (i : Fin (layers 0).count) (j : Fin (layers c.succ).count),
    ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) →
    ω.1 ∈ (layers 0).C i → ω.1 ∈ (layers c.succ).C j →
    ∀ z ∈ p.trueFiberBox k r m Hf Q ((layers 0).tag i),
      |eval ![z 0, z 2] ((layers c.succ).G j) - eval ![z 0, z 2] ((layers 0).G i) -
        p.canonicalOffset k r m (layers 0) (layers c.succ) Q i j| ≤
        p.N k ^ (-r - ![u, v] c)
  wit : Measure (α × ℝ)
  wit_le : wit ≤ p.μ k
  δ : ℝ
  δ_pos : 0 < δ
  good_witness : ∀ ω ∈ good, ∀ (a : Fin 3) (i : Fin (layers a).count), ω.1 ∈ (layers a).C i →
    ENNReal.ofReal (δ * (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-m) *
      (((2 : ℝ) ^ (-(p.T k r : ℤ))) * p.N k ^ (-p.ℓ * r)) *
      (p.N k ^ (-(![r, r + u, r + v] a))) ^ p.d)) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = (layers a).tag i 0} ≤
    wit (p.witnessSet k r (layers a) i (p.shortDomainCode k r ω))
  Knat : ℝ
  fwd : Fin (p.n k r) → (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) → Finset (Fin (layers 0).count)
  rev : Fin (layers 0).count → (Fin 2 → ℤ) × (ℤ × ℤ × ℤ) → Finset (Fin (p.n k r))
  fwd_card : ∀ Q c, ((fwd Q c).card : ℝ) ≤ Knat
  rev_card : ∀ i c, ((rev i c).card : ℝ) ≤ Knat
  good_native : ∀ ω ∈ good, ∀ (Q : Fin (p.n k r)) (i : Fin (layers 0).count),
    ω.1 ∈ p.B k r Q → ω.2 ∈ block (p.T k r) (p.j k r Q) → ω.1 ∈ (layers 0).C i →
    i ∈ fwd Q (p.shortComparisonCode k r m ω) ∧ Q ∈ rev i (p.shortComparisonCode k r m ω)
  smax : ℝ
  smax_fine : ∀ c : Fin 2, r + ![u, v] c ≤ smax
  band_cap : ∀ ω ∈ good, ∀ (G : MvPolynomial (Fin 2) ℝ) (x Δ : ℝ), G.totalDegree ≤ 2 →
    (∀ e, |G.coeff e| ≤ p.N k ^ (m / 1000)) → p.N k ^ (-smax) ≤ Δ →
    wit (p.comparisonBand k m ((2 : ℝ) ^ (-(p.T k r : ℤ))) (p.N k ^ (-p.ℓ * r))
      ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r))
      (![⌊p.b k ω.1 3 / p.N k ^ (-m)⌋, ⌊p.b k ω.1 0 / p.N k ^ (-m)⌋])
      (p.shortDomainCode k r ω) (G + MvPolynomial.C x) Δ) ≤
    ENNReal.ofReal (16800 * p.K k ^ 2 * p.N k ^ (-m) * (2 : ℝ) ^ (-(p.T k r : ℤ)) *
      ((2 : ℝ) ^ (-(p.T k r : ℤ)) * p.N k ^ (-p.ℓ * r)) * Δ ^ p.d) *
      p.π k {w : ℝ | ⌊w / p.N k ^ (-m)⌋ = ⌊p.b k ω.1 3 / p.N k ^ (-m)⌋}

namespace GoodTableData

variable {p} {k : ℕ} {r u v m H₀ Hf : ℝ} (t : p.GoodTableData k r u v m H₀ Hf)

include t in
theorem N_pos : 0 < p.N k := zero_lt_one.trans t.N_one

include t in
theorem K_nonneg : 0 ≤ p.K k := zero_le_one.trans t.K_one

/-- Original projected labels carry their major bins. -/
theorem label_tags {a : Fin 3} {i : Fin (t.layers a).count} {l : α}
    (hl : l ∈ (t.layers a).C i) :
    ⌊p.b k l 3 / p.N k ^ (-m)⌋ = (t.layers a).tag i 0 ∧
      ⌊p.b k l 0 / p.N k ^ (-m)⌋ = (t.layers a).tag i 1 := by
  have h := ((t.layer_valid a).2.2.2.2.2.1 i).2.2.2.1 l hl
  exact ⟨h.1, h.2.1⟩

/-- A label is determined by any of its points. -/
theorem label_unique {a : Fin 3} {i i' : Fin (t.layers a).count} {l : α}
    (hi : l ∈ (t.layers a).C i) (hi' : l ∈ (t.layers a).C i') : i = i' := by
  by_contra hne
  exact Set.disjoint_left.mp ((t.layer_valid a).2.2.2.2.1 i i' hne) hi hi'

/-- A good point lies in exactly one true label. -/
theorem true_unique {ω : α × ℝ} (hω : ω ∈ t.good) {Q Q' : Fin (p.n k r)}
    (hQ : ω.1 ∈ p.B k r Q) (hQt : ω.2 ∈ block (p.T k r) (p.j k r Q))
    (hQ' : ω.1 ∈ p.B k r Q') (hQt' : ω.2 ∈ block (p.T k r) (p.j k r Q')) : Q = Q' := by
  have h₁ := t.good_time ω hω Q hQt
  have h₂ := t.good_time ω hω Q' hQt'
  have hj : p.j k r Q = p.j k r Q' := by
    apply Fin.ext
    exact_mod_cast h₁.symm.trans h₂
  by_contra hne
  have hdisj := t.atDepth.2.2.2.1 Q Q' hne hj
  exact Set.disjoint_left.mp hdisj ((t.atDepth.2.2.1 Q).2.2 hQ) ((t.atDepth.2.2.1 Q').2.2 hQ')

theorem entry_unique (c : Fin 2) {ω : α × ℝ} (hω : ω ∈ t.good)
    {e e' : p.EntryTuple k r (t.layers 0) (t.layers c.succ)}
    (he : p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω)
    (he' : p.EntryMatches k r (t.layers 0) (t.layers c.succ) e' ω) : e = e' := by
  obtain ⟨Q, i, j, D⟩ := e
  obtain ⟨Q', i', j', D'⟩ := e'
  obtain ⟨hQ, hQt, hi, hj, hD⟩ := he
  obtain ⟨hQ', hQt', hi', hj', hD'⟩ := he'
  have h1 : Q = Q' := t.true_unique hω hQ hQt hQ' hQt'
  have h2 : i = i' := t.label_unique hi hi'
  have h3 : j = j' := t.label_unique hj hj'
  have h4 : D = D' := hD.symm.trans hD'
  subst h1 h2 h3 h4
  rfl

theorem exists_entry (c : Fin 2) {ω : α × ℝ} (hω : ω ∈ t.good) :
    ∃ e : p.EntryTuple k r (t.layers 0) (t.layers c.succ),
      p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω := by
  obtain ⟨Q, hQ, hQt⟩ := t.good_true ω hω
  obtain ⟨i, hi⟩ := t.good_label ω hω 0
  obtain ⟨j, hj⟩ := t.good_label ω hω c.succ
  exact ⟨(Q, i, j, p.shortDomainCode k r ω), hQ, hQt, hi, hj, rfl⟩

/-- The domain code of a matched good point is in the true menu. -/
theorem domain_mem_trueDomains (c : Fin 2) {ω : α × ℝ} (hω : ω ∈ t.good)
    {e : p.EntryTuple k r (t.layers 0) (t.layers c.succ)}
    (he : p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω) :
    e.2.2.2 ∈ p.trueDomains k r m e.1 ((t.layers 0).tag e.2.1) := by
  obtain ⟨hQ, hQt, hi, hj, hD⟩ := he
  rw [← hD]
  have htag := t.label_tags hi
  exact AtDepth.domainCode_mem_trueDomains p t.atDepth (N_pos t) (K_nonneg t) t.chi_width
    t.chi_slope e.1 ((t.layers 0).tag e.2.1) ((t.atDepth.2.2.1 e.1).2.2 hQ) htag.2 htag.1
    (t.good_time ω hω e.1 hQt)

open scoped Classical in
/-- The finite list of realized entries of fine color `c`. -/
def tuples (c : Fin 2) : Finset (p.EntryTuple k r (t.layers 0) (t.layers c.succ)) :=
  ((Finset.univ : Finset (Fin (p.n k r) × Fin (t.layers 0).count ×
      Fin (t.layers c.succ).count)).biUnion
    (fun x => (p.trueDomains k r m x.1 ((t.layers 0).tag x.2.1)).image
      (fun D => (x.1, x.2.1, x.2.2, D)))).filter
    (fun e => ∃ ω ∈ t.good, p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω)

theorem mem_tuples_iff (c : Fin 2) (e : p.EntryTuple k r (t.layers 0) (t.layers c.succ)) :
    e ∈ t.tuples c ↔ ∃ ω ∈ t.good, p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω := by
  classical
  constructor
  · intro he
    simp only [tuples, Finset.mem_filter] at he
    exact he.2
  · rintro ⟨ω, hω, hm⟩
    simp only [tuples, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    refine ⟨⟨(e.1, e.2.1, e.2.2.1), e.2.2.2, t.domain_mem_trueDomains c hω hm, rfl⟩, ω, hω, hm⟩

/-- The event of a realized entry: its good points. -/
def entryEvent (c : Fin 2) (e : p.EntryTuple k r (t.layers 0) (t.layers c.succ)) :
    Set (α × ℝ) :=
  t.good ∩ {ω | p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω}

theorem measurableSet_entryEvent (c : Fin 2)
    (e : p.EntryTuple k r (t.layers 0) (t.layers c.succ)) :
    MeasurableSet (t.entryEvent c e) := by
  have hB : MeasurableSet (p.B k r e.1) := (t.atDepth.2.2.1 e.1).2.1
  have hI : MeasurableSet (block (p.T k r) (p.j k r e.1)) := measurableSet_Icc
  have hA : MeasurableSet ((t.layers 0).C e.2.1) := (t.layer_valid 0).2.2.2.1 e.2.1
  have hF : MeasurableSet ((t.layers c.succ).C e.2.2.1) :=
    (t.layer_valid c.succ).2.2.2.1 e.2.2.1
  have hD : MeasurableSet {ω : α × ℝ | p.shortDomainCode k r ω = e.2.2.2} :=
    (p.measurable_shortDomainCode t.basic k r) (measurableSet_singleton _)
  refine t.good_measurable.inter ?_
  have h : {ω : α × ℝ | p.EntryMatches k r (t.layers 0) (t.layers c.succ) e ω} =
      (Prod.fst ⁻¹' p.B k r e.1) ∩ (Prod.snd ⁻¹' block (p.T k r) (p.j k r e.1)) ∩
        (Prod.fst ⁻¹' (t.layers 0).C e.2.1) ∩ (Prod.fst ⁻¹' (t.layers c.succ).C e.2.2.1) ∩
        {ω : α × ℝ | p.shortDomainCode k r ω = e.2.2.2} := by
    ext ω
    simp only [EntryMatches, Set.mem_setOf_eq, mem_inter_iff, mem_preimage, and_assoc]
  rw [h]
  exact ((((measurable_fst hB).inter (measurable_snd hI)).inter (measurable_fst hA)).inter
    (measurable_fst hF)).inter hD

/-- The number of realized entries of fine color `c`. -/
def count (c : Fin 2) : ℕ := (t.tuples c).card

/-- An enumeration of the realized entries. -/
def idx (c : Fin 2) (e : Fin (t.count c)) : p.EntryTuple k r (t.layers 0) (t.layers c.succ) :=
  ((t.tuples c).equivFin.symm e).val

theorem idx_mem (c : Fin 2) (e : Fin (t.count c)) : t.idx c e ∈ t.tuples c :=
  ((t.tuples c).equivFin.symm e).property

theorem idx_injective (c : Fin 2) : Function.Injective (t.idx c) := by
  intro e f h
  exact (t.tuples c).equivFin.symm.injective (Subtype.ext h)

theorem exists_idx (c : Fin 2) {e : p.EntryTuple k r (t.layers 0) (t.layers c.succ)}
    (he : e ∈ t.tuples c) : ∃ f, t.idx c f = e :=
  ⟨(t.tuples c).equivFin ⟨e, he⟩, by simp [idx]⟩

/-- Each enumerated entry has a good point realizing it. -/
theorem idx_realized (c : Fin 2) (e : Fin (t.count c)) :
    ∃ ω ∈ t.good, p.EntryMatches k r (t.layers 0) (t.layers c.succ) (t.idx c e) ω :=
  (t.mem_tuples_iff c _).mp (t.idx_mem c e)

theorem entryEvent_disjoint (c : Fin 2) :
    Pairwise (fun e f : Fin (t.count c) =>
      Disjoint (t.entryEvent c (t.idx c e)) (t.entryEvent c (t.idx c f))) := by
  intro e f hne
  apply Set.disjoint_left.mpr
  intro ω hωe hωf
  exact hne (t.idx_injective c (t.entry_unique c hωe.1 hωe.2 hωf.2))

theorem entryEvent_cover (c : Fin 2) :
    ∀ᵐ ω ∂t.law, ∃ e : Fin (t.count c), ω ∈ t.entryEvent c (t.idx c e) := by
  have hgood : ∀ᵐ ω ∂t.law, ω ∈ t.good := by
    rw [ae_iff]
    simpa only [compl_def, Set.mem_setOf_eq] using t.law_good
  filter_upwards [hgood] with ω hω
  obtain ⟨e, he⟩ := t.exists_entry c hω
  obtain ⟨f, hf⟩ := t.exists_idx c ((t.mem_tuples_iff c e).mpr ⟨ω, hω, he⟩)
  exact ⟨f, hω, by rw [hf]; exact he⟩

end GoodTableData
end Parent
end
end Submission.Obl.k4_general_wide_layer_offset_comparison
