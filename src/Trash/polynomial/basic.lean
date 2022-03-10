import category_theory.over
import category_theory.limits.shapes.pullbacks
import category_theory.adjunction.over

universes u₀ v₀

noncomputable theory

namespace category_theory

open limits

section pullback_functor

variables {C : Type u₀} [category.{v₀} C] [has_pullbacks C] {X Y : C}
/-
Pullback extends to a functor between over categories.
For the morphism map consider the following diagram
which uses `pullback.map`

            i.left
    E₀.left ⟶ E₁.left
        ↘        ↘
          Y  ──𝟙⟶   Y
        ↗        ↗
      X     ⟶   X
           𝟙

-/
/-- Pullback as a functor between over categories (also called base_change) -/
@[simps] def pullback_functor (f : X ⟶ Y) : over Y ⥤ over X :=
{ obj := λ g, over.mk (pullback.snd : (pullback g.hom f) ⟶ X),
  map := λ g₀ g₁ i, over.hom_mk (pullback.map _ _ _ _ i.left (𝟙 _) (𝟙 _) (by simp) (by simp)) (by simp) }

notation g `^*`:80 := pullback_functor g

end pullback_functor

namespace over

namespace terminal

variables {C : Type u₀} [category.{v₀} C] [has_terminal C]

/-
If category `C` has a terminal object then
`C` and `over ⊤_ C` (the overcategory of the terminal object)
are equivalent categories via the forgetful functor.
-/

/--
The inverse to the functor forgetting from the over category of the terminal object.
This leads to an equivalence in `is_equivalence_forget`.
-/
@[simp] def forget_inverse : C ⥤ over ⊤_ C :=
{ obj := λ X, over.mk (terminal.from X),
    map := λ X Y f, over.hom_mk f (by tidy) }

/-- On objects, the identity on `over ⊤_ C` is equal to the composition with `forget_inverse` -/
@[simp] def unit_iso_obj (X : over ⊤_ C) :
  X ≅ (over.forget (⊤_ C) ⋙ forget_inverse).obj X :=
eq_to_iso (by {cases X, congr, tidy})

/-- The identity on `over ⊤_ C` is naturally isomorphic to the composition with `forget_inverse` -/
def unit_iso : 𝟭 (over (⊤_ C)) ≅ over.forget (⊤_ C) ⋙ forget_inverse :=
nat_iso.of_components (λ X, unit_iso_obj X) (by tidy)

/-- The precomposition with the `forget_inverse` is naturally isomorphic to the identity on C -/
def counit_iso : forget_inverse ⋙ over.forget (⊤_ C) ≅ 𝟭 C :=
nat_iso.of_components (λ X, iso.refl _) (by tidy)

/-- The forgetful functor `over ⊤_ C → C` is an equivalence, with inverse `forget_inverse` -/
def is_equivalence_forget : is_equivalence (over.forget ⊤_ C) :=
is_equivalence.mk forget_inverse unit_iso counit_iso

variable [has_binary_products C]

/-- `forget_inverse` is naturally isomorphic to the general left adjoint to `over.forget` -/
def forget_inverse_iso_star : forget_inverse ≅ category_theory.star ⊤_ C :=
nat_iso.of_components
  (λ _, over.iso_mk (prod.left_unitor _).symm) -- X ≅ ⊤_ C ⨯ X
  (by tidy)

end terminal

end over

--- The actual file

variables {C : Type u₀} [category.{v₀} C] [has_pullbacks C] (W X Y Z : C)

/--
The data of a polynomial functor expressed as morphisms in a category with adjunction conditions.

     f     g     h
  W ←- X -→ Y -→ Z

The functor in question is then between over categories

         f^*                 Πg                        Σh
      (pullback)    (right adjoint to g^*)  (left adjoint to h^*)
  C/W   =====⥤  C/X      ========⥤      C/Y    =========⥤    C/Z

Σh always exists and is called `over.map`.
-/
structure polynomial :=
(f : X ⟶ W)
(g : X ⟶ Y)
(g_adj : is_left_adjoint (g^*))
(h : Y ⟶ Z)

namespace polynomial

variables {W X Y Z} (P : polynomial W X Y Z)

/-- The right adjoint to g^* from the polynomial. This is Πg in the literature -/
def g_right : over X ⥤ over Y := @is_left_adjoint.right _ _ _ _ (P.g^*) P.g_adj

/-
The left adjoint to `h^*` is `over.map P.h`. This is `Σg` in the literature.
The adjunction is given in `over_map_adj_pullback_functor`
-/
/-- The polynomial functor associated to the data of `category_theory.polynomial` -/
def functor : over W ⥤ over Z := P.f^* ⋙ P.g_right ⋙ over.map P.h

end polynomial





end category_theory
