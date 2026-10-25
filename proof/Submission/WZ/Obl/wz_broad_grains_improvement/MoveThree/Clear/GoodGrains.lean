-- Inlined from the package WangZahlLot (humanfia LOT tree wang_zahl_kakeya_dimH (Lean-Eval #2121)@da2150fe199f, ours (humanfia); WangZahlLot/ChallengeDeps.lean: lean-eval problem file; see NOTICE and LICENSES/wang-zahl-lot/): WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear.GoodGrains.
-- Changed: module names WangZahlLot.* -> Submission.WZ.* in imports and `open private ... from`.
/-
Adapted from this problem tree: o153, session x0686, branch x0619, commit fb5e50d.
Source: WangZahlLot/Obl/wz_broad_grains_move_three/Clear/GoodGrains.lean
The namespace and own-module imports are relocated for o122.
Credits to other same-tree contributors in the source are retained below.
-/
import Submission.WZ.Obl.wz_broad_grains_improvement.MoveThree.Clear.ClearCore

/-!
Ported (namespace and imports adjusted; `J` renamed to this desk's `Jt`, `Broad` taken from
`Defs`) from the o169 file `WangZahlLot/Obl/wz_move_three_wide_grains_core/GoodGrains.lean`,
branch x0641 of the o169 repository (workspace code, not accepted).
-/

set_option linter.unusedVariables false

/-!
# Step 4, first case, without the local factorisation: keeping the locally good grains

Given a stage-2 state of o169 (`J … 2`), call a grain `j` *locally good* (with constant `g'`)
when every convex `W` satisfies the frozen local count of `H` at `j`:
`#{j' : □(P_j') ⊆ 2□(P_j), U_j' ⊆ W} · a(ρc)c ≤ g' μ(W)`, the count running over *all* grains.

Removing every grain outside a set `Good` of locally good grains, and restricting each fine
shading `Z i` to the kept grain shadings of its own fibre, keeps every clause of `J`:
at a kept point the fibre sets `{i ∈ S | f i = k ∧ p ∈ Z i}` are unchanged, so the multiplicity
`[m, 2m]` and the fibre broadness are unchanged there (and both sides vanish elsewhere);
`N, a, ρ, c` and the cover are unchanged; the local count over the kept grains is at most the
count over all grains, so the local coefficient becomes `g'`. With `g' ≤ δ^(-ζ)` this is
`J … 3`, once the kept grains carry enough mass (`hmassH`, `hmassC`).
-/

noncomputable section

namespace WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear

/-- The body of `H` for given grain witnesses. -/
abbrev HB (d h:ℝ)(n:ℕ)(x v:Fin n→V)(S:Finset (Fin n))(Z:Fin n→Set V)(ρ:ℝ)(N:ℕ)(y w:Fin N→V)(f:Fin n→Fin N)(a c b g:ℝ)(L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(H:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ) : Prop :=
  (fun(U:Fin L→Set V)=>d≤a∧a≤ρ*c∧ρ*c≤c∧c≤1∧(∀j,M (H j)∧H j⊆U j∧U j⊆T ρ (y (γ j)) (w (γ j))∧ι (e j (w (γ j))) 0^2+ι (e j (w (γ j))) 1^2≤(10*ρ)^2)∧(∀j j',j≠j'→γ j=γ j'→Disjoint (H j) (H j'))∧(∀k,{p|∃j,γ j=k∧p∈H j}={p|∃i∈S,f i=k∧p∈Z i})∧O (d^h*L*a*(ρ*c)*c)≤∑j,μ (H j)∧(∀k p,(∃i∈S,f i=k∧p∈Z i)→q n {i|i∈S∧f i=k∧p∈Z i}∈Set.Icc m (2*m))∧(∀i∈S,∀j,f i=γ j→(Z i∩H j).Nonempty→Z i∩U j⊆H j∧(∀p∈T d (x i) (v i)∩frontier (U j),abs (ι (e j (p-z j)) 2)=c/2)∧∀t∈({-c/2,c/2}:Set ℝ),∃p∈T d (x i) (v i)∩U j,ι (e j (p-z j)) 2=t)∧b≤c∧∀j W,Convex ℝ W→O (q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧U j'⊆W}*(a*(ρ*c)*c))≤O g*μ W) (fun j=>P a (ρ*c) c (z j) (e j))

theorem H_iff {d h:ℝ}{n:ℕ}{x v:Fin n→V}{S:Finset (Fin n)}{Z:Fin n→Set V}{ρ:ℝ}{N:ℕ}{y w:Fin N→V}{f:Fin n→Fin N}{a c b g:ℝ} :
    H d h n x v S Z ρ N y w f a c b g ↔
      ∃ (L:ℕ)(z:Fin L→V)(e:Fin L→V≃ₗᵢ[ℝ]V)(Hs:Fin L→Set V)(γ:Fin L→Fin N)(m:ℝ),
        HB d h n x v S Z ρ N y w f a c b g L z e Hs γ m :=
  Iff.rfl


/-- `J` with its witnesses made explicit. -/
theorem J_iff {ω ζ d h ρ c b : ℝ} {n : ℕ} {x v : Fin n → V} {Y : Fin n → Set V} {j : ℕ} :
    Jt ω ζ d h ρ c b n x v Y j ↔
      ∃ (S : Finset (Fin n)) (Z : Fin n → Set V) (N : ℕ) (y w : Fin N → V) (f : Fin n → Fin N)
        (a g : ℝ), C d h n x v Y S Z ρ N y w f True ∧ d ^ (1 - ω / 100) ≤ ρ ∧ 0 < g ∧
        Broad ω ζ d h ρ n N v S Z f ∧ H d h n x v S Z ρ N y w f a c 0 g ∧ a < 2 * d ^ (1 - b) ∧
        ((1 ≤ j → d ^ ζ * (ρ / d) * N / n ≤ c) ∧ (2 ≤ j → ρ ≤ d ^ (ω / 100)) ∧
          (3 ≤ j → g ≤ d ^ (-ζ))) :=
  Iff.rfl

theorem Broad_mono {ω ζ d h h' ρ : ℝ} {n N : ℕ} {v : Fin n → V} {S : Finset (Fin n)}
    {Z : Fin n → Set V} {f : Fin n → Fin N}
    (hd : 0 < d) (hd1 : d ≤ 1) (hh : h ≤ h')
    (hb : Broad ω ζ d h ρ n N v S Z f) : Broad ω ζ d h' ρ n N v S Z f := by
  obtain ⟨-, hi⟩ := rpow_err_le hd hd1 hh
  intro k p u r hu hdr hrρ
  have hr : 0 < r := hd.trans_le hdr
  have hρ : 0 < ρ := hr.trans_le hrρ
  refine (hb k p u r hu hdr hrρ).trans (mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _))
  exact mul_le_mul_of_nonneg_right hi (Real.rpow_nonneg (div_nonneg hr.le hρ.le) _)

/-- The local count of the grains near `j` inside `W`, over all grains. -/
abbrev locCount (a ρ c : ℝ) {L : ℕ} (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (j : Fin L)
    (W : Set V) : ℝ :=
  q L {j'|P (a/ρ) c c (z j') (e j')⊆P (2*a/ρ) (2*c) (2*c) (z j) (e j)∧P a (ρ*c) c (z j') (e j')⊆W}

/-- `j` satisfies the frozen local count with constant `g`. -/
abbrev LocGood (a ρ c g : ℝ) {L : ℕ} (z : Fin L → V) (e : Fin L → V ≃ₗᵢ[ℝ] V) (j : Fin L) :
    Prop :=
  ∀ W, Convex ℝ W → O (locCount a ρ c z e j W * (a*(ρ*c)*c)) ≤ O g * μ W

/-- The fine shadings restricted to the kept grain shadings of their own fibre. -/
abbrev restrictZ {n N L : ℕ} (Z : Fin n → Set V) (f : Fin n → Fin N) (γ : Fin L → Fin N)
    (Hs : Fin L → Set V) (Good : Finset (Fin L)) (i : Fin n) : Set V :=
  Z i ∩ ⋃ j ∈ Good.filter (fun j => γ j = f i), Hs j

theorem mem_restrictZ {n N L : ℕ} {Z : Fin n → Set V} {f : Fin n → Fin N} {γ : Fin L → Fin N}
    {Hs : Fin L → Set V} {Good : Finset (Fin L)} {i : Fin n} {p : V} :
    p ∈ restrictZ Z f γ Hs Good i ↔ p ∈ Z i ∧ ∃ j ∈ Good, γ j = f i ∧ p ∈ Hs j := by
  simp only [restrictZ, Set.mem_inter_iff, Set.mem_iUnion, Finset.mem_filter, exists_prop]
  constructor
  · rintro ⟨h1, j, ⟨hj, hγ⟩, hp⟩
    exact ⟨h1, j, hj, hγ, hp⟩
  · rintro ⟨h1, j, hj, hγ, hp⟩
    exact ⟨h1, j, ⟨hj, hγ⟩, hp⟩

/-- Keeping a set of locally good grains turns a stage-2 state into a stage-3 state. -/
theorem stage_three_of_selected_good_grains
    {ω ζ δ η ε ρ c b g g' a m : ℝ} {n N L : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε) (hg'0 : 0 < g') (hg' : g' ≤ δ^(-ζ))
    (hC : C δ η n x v Y S Z ρ N y w f True) (hρ : δ^(1-ω/100) ≤ ρ)
    (hbr : Broad ω ζ δ η ρ n N v S Z f)
    (hHB : HB δ η n x v S Z ρ N y w f a c 0 g L z e Hs γ m)
    (hthin : a < 2*δ^(1-b)) (hlen : δ^ζ*(ρ/δ)*N/n ≤ c) (hρ2 : ρ ≤ δ^(ω/100))
    (Good : Finset (Fin L))
    (hgood : ∀ j ∈ Good, ∀ W, Convex ℝ W →
      O (q L {j' | j' ∈ Good ∧
        P (a/ρ) c c (z j') (e j') ⊆ P (2*a/ρ) (2*c) (2*c) (z j) (e j) ∧
        P a (ρ*c) c (z j') (e j') ⊆ W} * (a*(ρ*c)*c)) ≤ O g' * μ W)
    (hmassH : O (δ^ε*Good.card*a*(ρ*c)*c) ≤ ∑ j ∈ Good, μ (Hs j))
    (hmassC : O (δ^ε) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (restrictZ Z f γ Hs Good i)) :
    Jt ω ζ δ ε ρ c b n x v Y 3 := by
  obtain ⟨hda, hab, hbc, hc1, hgeom, hdisj, hunion, hmass, hmult, hcross, hb0, hcount⟩ := hHB
  have ha0 : 0 < a := hδ.trans_le hda
  have hρc0 : 0 < ρ * c := ha0.trans_le hab
  have hc0 : 0 < c := hρc0.trans_le hbc
  -- at a kept point of fibre `k`, the fibre sets of `Z` and of the restriction agree
  have key : ∀ (k : Fin N) (p : V), (∃ j ∈ Good, γ j = k ∧ p ∈ Hs j) → ∀ i, f i = k →
      (p ∈ restrictZ Z f γ Hs Good i ↔ p ∈ Z i) := by
    rintro k p ⟨j, hj, hγ, hp⟩ i hi
    rw [mem_restrictZ]
    exact ⟨fun h => h.1, fun h => ⟨h, j, hj, hγ.trans hi.symm, hp⟩⟩
  have keyset : ∀ (k : Fin N) (p : V), (∃ j ∈ Good, γ j = k ∧ p ∈ Hs j) →
      ∀ (R : Fin n → Prop),
      {i | i ∈ S ∧ f i = k ∧ p ∈ restrictZ Z f γ Hs Good i ∧ R i} =
        {i | i ∈ S ∧ f i = k ∧ p ∈ Z i ∧ R i} := by
    intro k p hk R
    ext i
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, (key k p hk i h2).1 h3, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, (key k p hk i h2).2 h3, h4⟩
  -- reindexing the kept grains
  let ι' : Fin Good.card → Fin L := fun k => (Good.equivFin.symm k).1
  have hι'mem : ∀ k, ι' k ∈ Good := fun k => (Good.equivFin.symm k).2
  have hι'inj : Function.Injective ι' := by
    intro k k' hkk
    have : Good.equivFin.symm k = Good.equivFin.symm k' := Subtype.ext hkk
    exact Good.equivFin.symm.injective this
  have hι'surj : ∀ j ∈ Good, ∃ k, ι' k = j := by
    intro j hj
    refine ⟨Good.equivFin ⟨j, hj⟩, ?_⟩
    simp [ι']
  have hsum : ∑ k, μ (Hs (ι' k)) = ∑ j ∈ Good, μ (Hs j) := by
    rw [← Finset.sum_coe_sort Good (fun j => μ (Hs j))]
    exact Equiv.sum_comp Good.equivFin.symm (fun j => μ (Hs j.1))
  obtain ⟨hz, hmC, hw, ht, hF, hT, hbal, hX, hov⟩ := cover_mono hδ hδ1 hηε hC
  have hbrε := Broad_mono hδ hδ1 hηε hbr
  refine ⟨S, restrictZ Z f γ Hs Good, N, y, w, f, a, g', ?_, hρ, hg'0, ?_, ?_, hthin,
    fun _ => hlen, fun _ => hρ2, fun _ => hg'⟩
  · -- the cover
    refine ⟨?_, hmassC, hw, ht, hF, hT, hbal, hX, hov⟩
    intro i
    obtain ⟨hzm, hzY, hzS⟩ := hz i
    refine ⟨hzm.inter (Finset.measurableSet_biUnion _ fun j _ => (hgeom j).1),
      Set.inter_subset_left.trans hzY, fun hi => ?_⟩
    simp only [restrictZ, hzS hi, Set.empty_inter]
  · -- broadness
    intro k p u r hu hdr hrρ
    by_cases hk : ∃ j ∈ Good, γ j = k ∧ p ∈ Hs j
    · have e1 := keyset k p hk (fun i => min ‖v i - u‖ ‖v i + u‖ ≤ r)
      have e2 := keyset k p hk (fun _ => True)
      simp only [and_true] at e2
      rw [e1, e2]
      exact hbrε k p u r hu hdr hrρ
    · have hempty : {i | i ∈ S ∧ f i = k ∧ p ∈ restrictZ Z f γ Hs Good i ∧
          min ‖v i - u‖ ‖v i + u‖ ≤ r} = ∅ := by
        ext i
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨-, hfi, hp, -⟩
        obtain ⟨-, j, hj, hγ, hpj⟩ := mem_restrictZ.1 hp
        exact hk ⟨j, hj, hγ.trans hfi, hpj⟩
      have hr : 0 < r := hδ.trans_le hdr
      have hρ0 : 0 < ρ := hr.trans_le hrρ
      rw [hempty]
      show ((∅ : Set (Fin n)).ncard : ℝ) ≤ _
      rw [Set.ncard_empty, Nat.cast_zero]
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hδ.le _)
        (Real.rpow_nonneg (div_nonneg hr.le hρ0.le) _)) (Nat.cast_nonneg _)
  · -- the grains
    refine ⟨Good.card, fun k => z (ι' k), fun k => e (ι' k), fun k => Hs (ι' k),
      fun k => γ (ι' k), m, hda, hab, hbc, hc1, fun k => hgeom (ι' k), ?_, ?_, ?_, ?_, ?_,
      hb0, ?_⟩
    · intro k k' hkk hγ
      exact hdisj (ι' k) (ι' k') (hι'inj.ne hkk) hγ
    · intro k
      ext p
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨k', hγ, hp⟩
        have hpk : p ∈ {p | ∃ j, γ j = k ∧ p ∈ Hs j} := ⟨ι' k', hγ, hp⟩
        rw [hunion k] at hpk
        obtain ⟨i, hi, hfi, hpi⟩ := hpk
        exact ⟨i, hi, hfi, mem_restrictZ.2 ⟨hpi, ι' k', hι'mem k', hγ.trans hfi.symm, hp⟩⟩
      · rintro ⟨i, hi, hfi, hp⟩
        obtain ⟨-, j, hj, hγ, hpj⟩ := mem_restrictZ.1 hp
        obtain ⟨k', rfl⟩ := hι'surj j hj
        exact ⟨k', hγ.trans hfi, hpj⟩
    · rw [hsum]
      exact hmassH
    · rintro k p ⟨i, hi, hfi, hp⟩
      obtain ⟨hpZ, j, hj, hγ, hpj⟩ := mem_restrictZ.1 hp
      have hk : ∃ j ∈ Good, γ j = k ∧ p ∈ Hs j := ⟨j, hj, hγ.trans hfi, hpj⟩
      have e2 := keyset k p hk (fun _ => True)
      simp only [and_true] at e2
      rw [e2]
      exact hmult k p ⟨i, hi, hfi, hpZ⟩
    · intro i hi k hfi hne
      have hne' : (Z i ∩ Hs (ι' k)).Nonempty := by
        obtain ⟨p, hp1, hp2⟩ := hne
        exact ⟨p, (mem_restrictZ.1 hp1).1, hp2⟩
      obtain ⟨hsub, hfr, hends⟩ := hcross i hi (ι' k) hfi hne'
      refine ⟨?_, hfr, hends⟩
      intro p hp
      exact hsub ⟨(mem_restrictZ.1 hp.1).1, hp.2⟩
    · intro k W hW
      refine le_trans ?_ (hgood (ι' k) (hι'mem k) W hW)
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hfin : Set.Finite {j' | j' ∈ Good ∧ P (a/ρ) c c (z j') (e j') ⊆
          P (2*a/ρ) (2*c) (2*c) (z (ι' k)) (e (ι' k)) ∧ P a (ρ*c) c (z j') (e j') ⊆ W} :=
        Set.toFinite _
      apply Nat.cast_le.mpr
      apply Set.ncard_le_ncard_of_injOn ι' ?_ hι'inj.injOn hfin
      intro k' hk'
      exact ⟨hι'mem k', hk'⟩

/-- Keeping a set of locally good grains turns a stage-2 state into a stage-3 state. -/
theorem stage_three_of_good_grains
    {ω ζ δ η ε ρ c b g g' a m : ℝ} {n N L : ℕ} {x v : Fin n → V} {Y : Fin n → Set V}
    {S : Finset (Fin n)} {Z : Fin n → Set V} {y w : Fin N → V} {f : Fin n → Fin N}
    {z : Fin L → V} {e : Fin L → V ≃ₗᵢ[ℝ] V} {Hs : Fin L → Set V} {γ : Fin L → Fin N}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hηε : η ≤ ε) (hg'0 : 0 < g') (hg' : g' ≤ δ^(-ζ))
    (hC : C δ η n x v Y S Z ρ N y w f True) (hρ : δ^(1-ω/100) ≤ ρ)
    (hbr : Broad ω ζ δ η ρ n N v S Z f)
    (hHB : HB δ η n x v S Z ρ N y w f a c 0 g L z e Hs γ m)
    (hthin : a < 2*δ^(1-b)) (hlen : δ^ζ*(ρ/δ)*N/n ≤ c) (hρ2 : ρ ≤ δ^(ω/100))
    (Good : Finset (Fin L))
    (hgood : ∀ j ∈ Good, LocGood a ρ c g' z e j)
    (hmassH : O (δ^ε*Good.card*a*(ρ*c)*c) ≤ ∑ j ∈ Good, μ (Hs j))
    (hmassC : O (δ^ε) * ∑ i, μ (Y i) ≤ ∑ i ∈ S, μ (restrictZ Z f γ Hs Good i)) :
    Jt ω ζ δ ε ρ c b n x v Y 3 := by
  apply stage_three_of_selected_good_grains hδ hδ1 hηε hg'0 hg' hC hρ hbr hHB
    hthin hlen hρ2 Good ?_ hmassH hmassC
  intro j hj W hW
  apply le_trans ?_ (hgood j hj W hW)
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right _ ?_
  · apply Nat.cast_le.mpr
    exact Set.ncard_le_ncard (fun j' hj' => hj'.2) (Set.toFinite _)
  · have ha : 0 < a := hδ.trans_le hHB.1
    have hrc : 0 < ρ * c := ha.trans_le hHB.2.1
    have hc : 0 < c := hrc.trans_le hHB.2.2.1
    positivity

end WangZahlLot.Obl.wz_broad_grains_improvement.MoveThree.Clear
