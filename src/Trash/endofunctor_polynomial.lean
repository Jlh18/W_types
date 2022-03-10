import category_theory.over
import polynomial.basic
import category_theory.adjunction.over
import category_theory.limits.types

universes u₀ u₁ v₀

noncomputable theory

namespace category_theory

namespace endofunctor

open limits

variables {C : Type u₀} [category.{v₀} C] [has_pullbacks C] [has_terminal C]

/--
The data of a polynomial endofunctor expressed as a morphism in a
category with a terminal object and adjunction conditions.

     !     g     !
  * ←- X -→ Y -→ *

The functor in question is then between over categories

         X × -              Πg                 Σ(y : Y) / forget
    (pullback of !)  (right adjoint to g^*)  (left adjoint to !^*)
  C    =====⥤  C/X      ========⥤      C/Y       ==========⥤    C
-/
structure polynomial (X Y : C) :=
(g : X ⟶ Y)
(g_adj : is_left_adjoint (g^*))

namespace polynomial

variables {X Y : C} (P : polynomial X Y)

@[simps] def to_polynomial : category_theory.polynomial (⊤_ C) X Y ⊤_ C :=
{ f := terminal.from X,
  g := P.g,
  g_adj := P.g_adj,
  h := terminal.from Y }

/-- The polynomial functor associated to the data of `category_theory.polynomial` -/
@[simps] def functor : C ⥤ C :=
over.terminal.forget_inverse ⋙ P.to_polynomial.functor ⋙ over.forget _

/-- Polynomial functors form a category, which may be regarded as a full subcategory of `C ⥤ C` -/
instance : category (Σ (X Y : C), polynomial X Y) :=
{ hom := λ P Q, nat_trans P.2.2.functor Q.2.2.functor,
  id := λ P, nat_trans.id _,
  comp := λ P Q R, nat_trans.vcomp }

end polynomial

namespace type

/-
The categorical way to view `g : over α` is a space over α,
generating an endofunctor `type.endofunctor`.
The W-type way to view this is `α` indexes some constructors, and `type.β g` gives their arities.
-/
variables {α : Type u₀} (g : over α)

/-
We are interested in the following polynomial functor

      g.left × -              Πg.hom                Σ(y : Y) / forget
    (pullback of !)  (right adjoint to g.hom^*)  (left adjoint to !^*)
  Set  =====⥤  Set/g.left  ========⥤        Set/α    ==========⥤   Set

-/

/--
`β a` is the preimage of `a : α` under `g.hom : g.left → α` (as a set coerced to a type),
this is the arity of constructor `a` from the perspective of W-types.
`β` converts a bundle `g : over α` into a dependent type `β g : α → Type`.
The converse of `β` is `endofunctor.bundle`
-/
@[simp] def β (a : α) : Type u₀ := { x : g.left // g.hom x = a }

/--
`bundle` works the other way, converting any dependent type `β : α → Type` into
a bundle in the over category `over α`.
We must lift everything to the maximum universe level.
-/
@[simps] def bundle (β : α → Type u₀) : over α := over.mk (@sigma.fst α β)

/--
A map between bundles `p` and `q` induces a map between the bundles of section spaces,
this forms the map in `endofunctor.type.pi`.
-/
@[simp] def bundle_map (p q : over g.left) (f : p ⟶ q) :
  sigma (λ (a : α), Π (b : β g a), β p b.val) → sigma (λ (a : α), Π (b : β g a), β q b.val) :=
λ σ, ⟨ σ.1, λ b, ⟨ f.1 (σ.2 b).1 ,
  by { obtain ⟨ hf, hσ ⟩ := ⟨ congr_fun f.w, (σ.snd b).2 ⟩, dsimp at hf hσ, simp [f.w, hf, hσ] } ⟩⟩

/-- The left adjoint Πg of `pullback_functor g`, taking objects to the bundle of section spaces -/
@[simps] def pi : over g.left ⥤ over α :=
{ obj := λ p, bundle (λ a, Π (b : β g a), β p b.val),
  map := λ p q f, over.hom_mk $ bundle_map _ p q f }.

/-- The adjunction Πg ⊣ `pullback_functor` -/
def pi_adj_pullback_functor : pullback_functor g.hom ⊣ pi g :=
sorry

/-- The polynomial endofunctor given by a -/
@[simps] def polynomial : endofunctor.polynomial g.left α :=
{ g := g.hom,
  g_adj := is_left_adjoint.mk (pi g) (pi_adj_pullback_functor g) }

end type


end endofunctor



end category_theory
