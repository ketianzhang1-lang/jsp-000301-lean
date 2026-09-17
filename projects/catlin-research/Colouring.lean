import GraphCore

namespace CatlinComplete
open Finset CatlinCertificates

def eightColouring : graph.Coloring (Fin 8) :=
  SimpleGraph.Coloring.mk (fun v => ⟨colour v, eight_colours v⟩) (by
    intro u v h heq
    exact proper_eight_colouring u v h (congrArg Fin.val heq))

theorem colour_fiber_card_le_two (C : graph.Coloring (Fin 7)) (c : Fin 7) :
    ((univ : Finset Vertex).filter fun v => C v = c).card ≤ 2 := by
  by_contra hn
  have hlt : 2 < ((univ : Finset Vertex).filter fun v => C v = c).card := by omega
  obtain ⟨x, hx, y, hy, z, hz, hxy, hxz, hyz⟩ := Finset.two_lt_card.mp hlt
  have hxc := (Finset.mem_filter.mp hx).2
  have hyc := (Finset.mem_filter.mp hy).2
  have hzc := (Finset.mem_filter.mp hz).2
  rcases no_independent_triple x y z hxy hxz hyz with h | h | h
  · exact (C.valid h) (hxc.trans hyc.symm)
  · exact (C.valid h) (hxc.trans hzc.symm)
  · exact (C.valid h) (hyc.trans hzc.symm)

theorem not_seven_colorable : ¬graph.Colorable 7 := by
  rintro ⟨C⟩
  have hsum : (15 : ℕ) = ∑ c : Fin 7,
      ((univ : Finset Vertex).filter fun v => C v = c).card := by
    simpa using (Finset.sum_card_fiberwise_eq_card_filter
      (univ : Finset Vertex) (univ : Finset (Fin 7)) C).symm
  have hle : (∑ c : Fin 7,
      ((univ : Finset Vertex).filter fun v => C v = c).card) ≤ ∑ _c : Fin 7, 2 := by
    exact Finset.sum_le_sum fun c _ => colour_fiber_card_le_two C c
  norm_num at hle
  omega

theorem chromaticNumber_eq_eight : graph.chromaticNumber = 8 := by
  have h : graph.chromaticNumber = (7 : ℕ∞) + 1 :=
    SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable.mpr
      ⟨⟨eightColouring⟩, not_seven_colorable⟩
  convert h using 1
  norm_num

end CatlinComplete
