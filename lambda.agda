-- Basic
data ⊥ : Set where
data ⊤ : Set where
  tt : ⊤
data _⊎_ (A : Set) (B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B
data ∃ {A} (P : A → Set) : Set where
  _,_ : ∀ x → P x → ∃ P

¬_ : Set → Set
¬ A = A → ⊥
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : ¬ P → Dec P

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x
sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym refl = refl
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
cong : ∀ {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

⊥-elim : ∀ {A : Set} → ⊥ → A
⊥-elim ()
_≠_ : ∀ {A : Set} → A → A → Set
x ≠ y = ¬ (x ≡ y)
≠-refl : ∀ {A B} {x : A} → x ≠ x → B
≠-refl eq = ⊥-elim (eq refl)
≠-sym : ∀ {A} {x y : A} → x ≠ y → y ≠ x
≠-sym neq eq = neq (sym eq)

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ
_≟_ : ∀ (x y : ℕ) → Dec (x ≡ y)
zero ≟ zero = yes refl
zero ≟ suc y = no (λ())
suc x ≟ zero = no (λ())
suc x ≟ suc y with x ≟ y
... | yes refl = yes refl
... | no neq = no (λ x1 → neq (neq2 x1))
  where
    neq2 : suc x ≡ suc y → x ≡ y
    neq2 refl = refl

Id : Set
Id = ℕ

infixr 7 _⇒_

data Type : Set where
  `bool                   :  Type
  _⇒_                     :  Type → Type → Type

infix  5  ƛ_⦂_⇒_
infixl 7  _·_
infix  8  `if_then_else_
infix  9  `_

data Term : Set where
  `_                      :  Id → Term
  ƛ_⦂_⇒_                  :  Id -> Type → Term → Term
  _·_                     :  Term → Term → Term
  `true                   :  Term
  `false                  :  Term
  `if_then_else_          :  Term → Term → Term → Term

data Value : Term → Set where
  V-ƛ : ∀ {x T t} → Value (ƛ x ⦂ T ⇒ t)
  V-true : Value `true
  V-false : Value `false

infix 9 _[_:=_]

_[_:=_] : Term → Id → Term → Term
(` x) [ y := V ] with x ≟ y
... | yes _ = V
... | no _ = ` x
(ƛ x ⦂ T ⇒ t) [ y := V ] with x ≟ y
... | yes _ = ƛ x ⦂ T ⇒ t
... | no _ = ƛ x ⦂ T ⇒ (t [ y := V ])
(L · R) [ y := V ] = (L [ y := V ]) · (R [ y := V ])
`true [ y := V ] = `true
`false [ y := V ] = `false
(`if C then T else E) [ y := V ] = `if (C [ y := V ]) then (T [ y := V ]) else (E [ y := V ])

infix 4 _—→_

data _—→_ : Term → Term → Set where
  ξ-·₁ : ∀ {L L′ M}
    → L —→ L′
    → L · M —→ L′ · M
  ξ-·₂ : ∀ {V M M′}
    → Value V
    → M —→ M′
    → V · M —→ V · M′
  β-· : ∀ {x T N V}
    → Value V
    → (ƛ x ⦂ T ⇒ N) · V —→ N [ x := V ]

  ξ-if : ∀ {L L′ M N}
    → L —→ L′
    → `if L then M else N —→ `if L′ then M else N
  β-if-true : ∀ {M N}
    → `if `true then M else N —→ M
  β-if-false : ∀ {M N}
    → `if `false then M else N —→ N

Context : Set
Context = Id → (Type ⊎ ⊤)

infixl 5 _,_⦂_
_,_⦂_ : Context → Id → Type → Context
(Γ , x ⦂ T) y with y ≟ x
...| yes _ = inj₁ T
...| no  _ = Γ y

infix 4 _⊢_⦂_
data _⊢_⦂_ : Context → Term → Type → Set where
  ⊢` : ∀ {Γ x T}
    → Γ x ≡ inj₁ T
    → Γ ⊢ ` x ⦂ T
  ⊢ƛ : ∀ {Γ x T t U}
    → Γ , x ⦂ T ⊢ t ⦂ U
    → Γ ⊢ ƛ x ⦂ T ⇒ t ⦂ T ⇒ U
  ⊢· : ∀ {Γ L M T U}
    → Γ ⊢ L ⦂ T ⇒ U
    → Γ ⊢ M ⦂ T
    → Γ ⊢ L · M ⦂ U
  ⊢true : ∀ {Γ}
    → Γ ⊢ `true ⦂ `bool
  ⊢false : ∀ {Γ}
    → Γ ⊢ `false ⦂ `bool
  ⊢if : ∀ {Γ L M N T}
    → Γ ⊢ L ⦂ `bool
    → Γ ⊢ M ⦂ T
    → Γ ⊢ N ⦂ T
    → Γ ⊢ `if L then M else N ⦂ T

empty : Context
empty x = inj₂ tt

data Progress (M : Term) : Set where
  step : ∀ {N}
    → M —→ N
    → Progress M
  done :
      Value M
      ----------
    → Progress M

progress : ∀ {M T}
  → empty ⊢ M ⦂ T
  → Value M ⊎ ∃ (λ M′ → M —→ M′)
progress (⊢ƛ ⊢N) = inj₁ V-ƛ
progress (⊢· ⊢L ⊢M) with progress ⊢L
... | inj₂ ( _ , S ) = inj₂ ( _ , (ξ-·₁ S) )
... | inj₁ V-ƛ with progress ⊢M
...   | inj₂ ( _ , S ) = inj₂ ( _ , (ξ-·₂ V-ƛ S) )
...   | inj₁ VM = inj₂ ( _ , (β-· VM) )
progress ⊢true = inj₁ V-true
progress ⊢false = inj₁ V-false
progress (⊢if C T F) with progress C
... | inj₂ ( _ , S ) = inj₂ ( _ , (ξ-if S) )
... | inj₁ V-true = inj₂ ( _ , β-if-true )
... | inj₁ V-false = inj₂ ( _ , β-if-false )

map≡ : Context → Context → Set
map≡ Γ Γ′ = ∀ x → Γ x ≡ Γ′ x

upd≡ : ∀ {Γ Γ′ x T} → map≡ Γ Γ′ → map≡ (Γ , x ⦂ T) (Γ′ , x ⦂ T)
upd≡ {_} {_} {x} equ y with y ≟ x
... | yes refl = refl
... | no _ = equ y

shadow≡ : ∀ {Γ x v1 v2} → map≡ (Γ , x ⦂ v1 , x ⦂ v2) (Γ , x ⦂ v2)
shadow≡ {Γ} {y} {v1} {v2} x with x ≟ y
shadow≡ {Γ} {y} {v1} {v2} x | yes refl = refl
shadow≡ {Γ} {y} {v1} {v2} x | no _ with x ≟ y
shadow≡ {Γ} {y} {v1} {v2} x | no neq | yes refl = ≠-refl neq
shadow≡ {Γ} {y} {v1} {v2} x | no _ | no _ = refl

permute≡ : ∀ {Γ x y} → (x ≡ y → ⊥) → ∀ {v1 v2} → map≡ (Γ , x ⦂ v1 , y ⦂ v2) (Γ , y ⦂ v2 , x ⦂ v1)
permute≡ {_} {x} {y} neq z with z ≟ x | z ≟ y
permute≡ {_} {x} {y} neq z | yes refl | yes refl = ≠-refl neq
permute≡ {_} {x} {y} neq z | yes refl | no neq2 with x ≟ x
permute≡ {_} {x} {y} neq z | yes refl | no neq2 | yes _ = refl
permute≡ {_} {x} {y} neq z | yes refl | no neq2 | no neq1 = ≠-refl neq1
permute≡ {_} {x} {y} neq z | no neq1 | yes refl with y ≟ y
permute≡ {_} {x} {y} neq z | no neq1 | yes refl | yes _ = refl
permute≡ {_} {x} {y} neq z | no neq1 | yes refl | no neq2 = ≠-refl neq2
permute≡ {_} {x} {y} neq z | no neq1 | no neq2 with z ≟ x | z ≟ y
permute≡ {_} {x} {y} neq z | no neq1 | no neq2 | yes refl | _ = ≠-refl neq1
permute≡ {_} {x} {y} neq z | no neq1 | no neq2 | no neq3  | yes refl = ≠-refl neq2
permute≡ {_} {x} {y} neq z | no neq1 | no neq2 | no neq3  | no neq4 = refl

_⊆_ : Context → Context → Set
Γ ⊆ Γ′ = ∀ x v → Γ x ≡ inj₁ v → Γ′ x ≡ inj₁ v

⊆-update : ∀ {Γ Γ′ x T} → Γ ⊆ Γ′ → (Γ , x ⦂ T) ⊆ (Γ′ , x ⦂ T)
⊆-update {_} {_} {x} ⊆ y v eq with y ≟ x
⊆-update {_} {_} {x} ⊆ y v eq | yes _ = eq
⊆-update {_} {_} {x} ⊆ y v eq | no _ = ⊆ y v eq

weak : ∀ {Γ Γ'} → Γ ⊆ Γ' → ∀ {t} {T} → Γ ⊢ t ⦂ T → Γ' ⊢ t ⦂ T
weak {Γ} {Γ'} ⊆Γ (⊢` x) = ⊢` (⊆Γ _ _ x)
weak {Γ} {Γ'} ⊆Γ (⊢ƛ ⊢) = ⊢ƛ (weak (⊆-update ⊆Γ) ⊢)
weak {Γ} {Γ'} ⊆Γ (⊢· ⊢ ⊢₁) = ⊢· (weak ⊆Γ ⊢) (weak ⊆Γ ⊢₁)
weak {Γ} {Γ'} ⊆Γ ⊢true = ⊢true
weak {Γ} {Γ'} ⊆Γ ⊢false = ⊢false
weak {Γ} {Γ'} ⊆Γ (⊢if ⊢ ⊢₁ ⊢₂) = ⊢if (weak ⊆Γ ⊢) (weak ⊆Γ ⊢₁) (weak ⊆Γ ⊢₂)

⊂-refl : ∀ {Γ Γ'} → (map≡ Γ Γ') → (Γ ⊆ Γ')
⊂-refl equ x v eq = trans (sym (equ x)) eq

cong≡ : ∀ {Γ Γ′} → map≡ Γ Γ′ → ∀ {t} {T} → Γ ⊢ t ⦂ T → Γ′ ⊢ t ⦂ T
cong≡ equ ⊢ = weak (⊂-refl equ) ⊢

weak-∅ : ∀ {Γ} → ∀ {t} {T} → empty ⊢ t ⦂ T → Γ ⊢ t ⦂ T
weak-∅ {Γ} ⊢ = weak (λ x v ()) ⊢

subst⊢ : ∀ {Γ x T t U V}
  → empty ⊢ V ⦂ T
  → Γ , x ⦂ T ⊢ t ⦂ U
  → Γ ⊢ t [ x := V ] ⦂ U
subst⊢ {_} {x} ⊢V (⊢` {_} {y} ∈) with y ≟ x
subst⊢ {_} {x} ⊢V (⊢` {_} {y} refl) | yes refl = weak-∅ ⊢V
subst⊢ {_} {x} ⊢V (⊢` {_} {y} ∈) | no _ = ⊢` ∈
subst⊢ {_} {x} ⊢V (⊢ƛ {_} {y} ⊢t) with y ≟ x | ⊢t
subst⊢ ⊢V (⊢ƛ ⊢t) | yes refl | _ = ⊢ƛ (cong≡ shadow≡ ⊢t)
subst⊢ {Γ} ⊢V (⊢ƛ ⊢t) | no neq     | _ = ⊢ƛ (subst⊢ ⊢V (cong≡ (permute≡ (≠-sym neq)) ⊢t))
subst⊢ ⊢V (⊢· ⊢t ⊢t₁) = ⊢· (subst⊢ ⊢V ⊢t) (subst⊢ ⊢V ⊢t₁)
subst⊢ ⊢V ⊢true = ⊢true
subst⊢ ⊢V ⊢false = ⊢false
subst⊢ ⊢V (⊢if ⊢t ⊢t₁ ⊢t₂) = ⊢if (subst⊢ ⊢V ⊢t) (subst⊢ ⊢V ⊢t₁) (subst⊢ ⊢V ⊢t₂)

preserve : ∀ {t t' T} → empty ⊢ t ⦂ T → t —→ t' → empty ⊢ t' ⦂ T
preserve (⊢· ⊢ ⊢₁) (ξ-·₁ ——) = ⊢· (preserve ⊢ ——) ⊢₁
preserve (⊢· ⊢ ⊢₁) (ξ-·₂ x ——) = ⊢· ⊢ (preserve ⊢₁ ——)
preserve (⊢· (⊢ƛ ⊢) ⊢₁) (β-· x) = subst⊢ ⊢₁ ⊢
preserve (⊢if ⊢ ⊢₁ ⊢₂) (ξ-if ——) = ⊢if (preserve ⊢ ——) ⊢₁ ⊢₂
preserve (⊢if ⊢ ⊢₁ ⊢₂) β-if-true = ⊢₁
preserve (⊢if ⊢ ⊢₁ ⊢₂) β-if-false = ⊢₂