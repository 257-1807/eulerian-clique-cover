module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic

public section

namespace CliqueCover

open SimpleGraph

/-- The least number of colors in a proper coloring of the complement:
the color classes partition the vertices into cliques of the original graph. -/
noncomputable def vertexCliqueCoverNumber {V : Type*} (G : SimpleGraph V) : ℕ :=
  sInf {k : ℕ | Gᶜ.Colorable k}

/-- GraphCalc maximizes over triples of distinct vertices, returning zero if none exist. -/
noncomputable def triameter {V : Type*} [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact (Finset.univ : Finset (V × V × V)).sup fun (a, b, c) =>
    if a ≠ b ∧ b ≠ c ∧ a ≠ c then G.dist a b + G.dist b c + G.dist a c else 0

/-- On a finite undirected graph, the source requires connectivity and even degrees. -/
def IsEulerian {V : Type*} (G : SimpleGraph V) : Prop :=
  G.Connected ∧ ∀ v, Even (G.neighborSet v).ncard

abbrev exampleGraph (n : ℕ) := completeBipartiteGraph (Fin 2) (Fin n)

private theorem across {n : ℕ} (i : Fin 2) (j : Fin n) :
    (exampleGraph n).Adj (.inl i) (.inr j) := by simp [exampleGraph]

theorem connected {n : ℕ} (hn : 0 < n) : (exampleGraph n).Connected := by
  apply ((exampleGraph n).connected_iff_exists_forall_reachable).mpr
  refine ⟨Sum.inl 0, ?_⟩
  rintro (a | b)
  · let j : Fin n := ⟨0, hn⟩
    exact (across 0 j).reachable.trans (across a j).reachable.symm
  · exact (across 0 b).reachable

theorem eulerian {n : ℕ} (hn : 0 < n) (he : Even n) : IsEulerian (exampleGraph n) := by
  refine ⟨connected hn, ?_⟩
  rintro (i | j)
  · have h : (exampleGraph n).neighborSet (.inl i) = Set.range (Sum.inr : Fin n → Fin 2 ⊕ Fin n) := by
      ext x
      cases x <;> simp [SimpleGraph.mem_neighborSet, exampleGraph]
    simpa [h, Set.ncard_range_of_injective Sum.inr_injective] using he
  · have h : (exampleGraph n).neighborSet (.inr j) = Set.range (Sum.inl : Fin 2 → Fin 2 ⊕ Fin n) := by
      ext x
      cases x <;> simp [SimpleGraph.mem_neighborSet, exampleGraph]
    simp [h, Set.ncard_range_of_injective Sum.inl_injective]

theorem cover_eq {n : ℕ} (hn : 2 ≤ n) : vertexCliqueCoverNumber (exampleGraph n) = n := by
  let c : (exampleGraph n)ᶜ.Coloring (Fin n) :=
    Coloring.mk (Sum.elim (Fin.castLE hn) id) (by
      rintro (x | x) (y | y) hadj <;>
        simp_all [SimpleGraph.compl_adj, exampleGraph])
  have hc : (exampleGraph n)ᶜ.Colorable n := ⟨c⟩
  apply Nat.le_antisymm (Nat.sInf_le (s := {k | (exampleGraph n)ᶜ.Colorable k}) hc)
  have hmin : (exampleGraph n)ᶜ.Colorable (vertexCliqueCoverNumber (exampleGraph n)) :=
    Nat.sInf_mem (s := {k | (exampleGraph n)ᶜ.Colorable k}) ⟨n, hc⟩
  obtain ⟨color⟩ := hmin
  have inject := color.injective_comp_of_pairwise_adj (Sum.inr : Fin n → Fin 2 ⊕ Fin n) (by
    intro i j hij
    simp [SimpleGraph.compl_adj, exampleGraph, hij])
  change n ≤ vertexCliqueCoverNumber (exampleGraph n)
  simpa using Fintype.card_le_of_injective _ inject

private theorem dist_le_two {n : ℕ} (hn : 0 < n) (u v : Fin 2 ⊕ Fin n) :
    (exampleGraph n).dist u v ≤ 2 := by
  cases u with
  | inl x =>
    cases v with
    | inl y =>
      let j : Fin n := ⟨0, hn⟩
      exact SimpleGraph.dist_le (Walk.cons (across x j) (.cons (across y j).symm .nil))
    | inr y => simp [dist_eq_one_iff_adj.mpr (across x y)]
  | inr x =>
    cases v with
    | inl y => simp [dist_eq_one_iff_adj.mpr (across y x).symm]
    | inr y => exact SimpleGraph.dist_le (Walk.cons (across 0 x).symm (.cons (across 0 y) .nil))

private theorem right_dist {n : ℕ} {i j : Fin n} (hij : i ≠ j) :
    (exampleGraph n).dist (.inr i) (.inr j) = 2 := by
  rw [SimpleGraph.dist, edist_eq_two_iff.mpr]
  · rfl
  · refine ⟨by simpa using hij, by simp [exampleGraph], Sum.inl 0, ?_⟩
    exact ⟨(across 0 i).symm, (across 0 j).symm⟩

theorem triameter_eq {n : ℕ} (hn : 3 ≤ n) : triameter (exampleGraph n) = 6 := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b, c⟩ _
    dsimp only
    split
    · have hpos : 0 < n := by omega
      have h₁ := dist_le_two hpos a b
      have h₂ := dist_le_two hpos b c
      have h₃ := dist_le_two hpos a c
      omega
    · decide
  · let i : Fin n := ⟨0, by omega⟩
    let j : Fin n := ⟨1, by omega⟩
    let k : Fin n := ⟨2, by omega⟩
    have hij : i ≠ j := by simp [i, j]
    have hjk : j ≠ k := by simp [j, k]
    have hik : i ≠ k := by simp [i, k]
    unfold triameter
    let p : (Fin 2 ⊕ Fin n) × (Fin 2 ⊕ Fin n) × (Fin 2 ⊕ Fin n) := (.inr i, .inr j, .inr k)
    apply le_trans _ (Finset.le_sup (Finset.mem_univ p))
    simp [p, right_dist, hij, hjk, hik]

/-- Formal negation of Pastorek's candidate for every finite graph. -/
theorem refute_5065dd93 :
    ¬ (∀ (V : Type) [Fintype V] (G : SimpleGraph V), 2 ≤ Fintype.card V →
      IsEulerian G → vertexCliqueCoverNumber G ≤ triameter G + 4) := by
  intro hall
  have h := hall (Fin 2 ⊕ Fin 12) (exampleGraph 12) (by decide)
    (eulerian (by decide) (by decide))
  rw [cover_eq (by decide), triameter_eq (by decide)] at h
  omega

/-- At fixed triameter six, clique cover numbers of finite Eulerian graphs are unbounded. -/
theorem unbounded_at_six (C : ℕ) :
    ∃ (n : ℕ), IsEulerian (exampleGraph n) ∧ triameter (exampleGraph n) = 6 ∧
      C < vertexCliqueCoverNumber (exampleGraph n) := by
  let n := 2 * (C + 2)
  have hn : 3 ≤ n := by dsimp [n]; omega
  refine ⟨n, eulerian (by omega) ⟨C + 2, by simp [n, two_mul]⟩, triameter_eq hn, ?_⟩
  rw [cover_eq (by omega)]
  dsimp [n]
  omega

end CliqueCover

#print axioms CliqueCover.refute_5065dd93
#print axioms CliqueCover.unbounded_at_six
