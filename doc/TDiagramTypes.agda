module TDiagramTypes where

data ∃ (A : Set) (B : A -> Set) : Set where
    _,_ : (a : A) -> (b : B a) -> ∃ A B
fst : ∀ {A B} -> ∃ A B -> A
fst (a , b) = a
snd : ∀ {A B} -> (p : ∃ A B) -> B (fst p)
snd (a , b) = b

choice : {A C : Set} {B : A -> Set} -> ((a : A) -> B a -> C) -> ∃ A B -> C
choice f (a , b) = f a b

data ℕ : Set where
    Zero : ℕ
    Succ : ℕ -> ℕ
{-# BUILTIN NATURAL ℕ #-}

data ⊥ : Set where
data T : Set where
    triv : T
¬_ : Set -> Set
¬_ x = x -> ⊥
exfalso : {A : Set} -> ⊥ -> A
exfalso()
data _≡_ {X : Set} (x : X) : X -> Set where
    Refl : x ≡ x
_≠_ : {X : Set} -> X -> X -> Set
x ≠ y = ¬ (x ≡ y)
data Decide (A : Set) : Set where
    Yes : A -> Decide A
    No : ¬ A -> Decide A

succInj : ∀{n m} -> Succ n ≡ Succ m -> n ≡ m
succInj Refl = Refl

_==_ : (n m : ℕ) -> Decide (n ≡ m)
Zero == Zero = Yes Refl
Zero == Succ m = No (λ ())
Succ n == Zero = No (λ ())
Succ n == Succ m with n == m
Succ n == Succ m | No p = No (λ q → p (succInj q))
Succ n == Succ .n | Yes Refl = Yes Refl

-- The diagrams as specified in the exercise.
data Diagram : Set where
    -- Atomic diagrams.
    Program : (L : ℕ) -> Diagram
    Platform : (L : ℕ) -> Diagram
    Interpreter : (L M : ℕ) -> Diagram
    Compiler : (L M N : ℕ) -> Diagram
    -- Composed diagrams.
    Execute : Diagram -> Diagram -> Diagram
    Compile : Diagram -> Diagram -> Diagram

-- Determines what can be stacked on the bottom of this diagram.
data Requires : Set where
    ReqN : Requires -- Nothing more can be required, i.e. the bottom is a Platform.
    ReqY : (L : ℕ) -> Requires -- You can stack something that provides L on the bottom.

-- Determines what can be stacked on the top (or next to) this diagram.
data Provides : Set where
    ProN : Provides -- Nothing more can be stacked, i.e. the top is a Program.
    ProY : (L : ℕ) -> Provides -- You can stack something that requires L on the top.
    ProC : (L : ℕ) -> (M : ℕ) -> Provides -- You can stack something that requires L on the side, and the result can stack M on the bottom.

infix 20 _=>_

data Type : Set where
    _=>_ : Requires -> Provides -> Type

infix 10 _::_
data _::_ : Diagram -> Type -> Set where
    -- Type judgements for atomic diagrams.
    prog : ∀ {L} -> Program L :: ReqY L => ProN
    plat : ∀ {L} -> Platform L :: ReqN => ProY L
    intr : ∀ {L M} -> Interpreter L M :: ReqY L => ProY M
    cmpr : ∀ {L M N} -> Compiler L M N :: ReqY L => ProC M N
    -- Type judgements for composite diagrams.
    exec : ∀ {L M N D₁ D₂} -> D₁ :: ReqY L => M -> D₂ :: N => ProY L -> Execute D₁ D₂ :: N => M
    comp : ∀ {L M N O D₁ D₂} -> D₁ :: ReqY L => M -> D₂ :: N => ProC L O -> Compile D₁ D₂ :: ReqY O => M

typeUnique : ∀ D {T₀ T₁} -> D :: T₀ -> D :: T₁ -> T₀ ≡ T₁
typeUnique .(Program _) prog prog = Refl
typeUnique .(Platform _) plat plat = Refl
typeUnique .(Interpreter _ _) intr intr = Refl
typeUnique .(Compiler _ _ _) cmpr cmpr = Refl
typeUnique (Execute D₁ D₂) (exec x₀ x₁) (exec x₂ x₃) with typeUnique D₁ x₀ x₂ | typeUnique D₂ x₁ x₃
typeUnique (Execute D₁ D₂) (exec x₀ x₁) (exec x₂ x₃) | Refl | Refl = Refl
typeUnique (Compile D₁ D₂) (comp x₀ x₁) (comp x₂ x₃) with typeUnique D₁ x₀ x₂ | typeUnique D₂ x₁ x₃
typeUnique (Compile D₁ D₂) (comp x₀ x₁) (comp x₂ x₃) | Refl | Refl = Refl

-- Prove that this type system rejects nonsensical types
nonsense : Diagram -> Set
nonsense D = (T : Type) -> ¬(D :: T)

claim1 : ∀ L D -> nonsense (Execute (Platform L) D)
claim1 L D .(_ => _) (exec () x₁)

claim2a : ∀ L D -> nonsense (Execute D (Program L))
claim2a L D .(_ => _) (exec x ())
claim2b : ∀ L M N D -> nonsense (Execute D (Compiler L M N))
claim2b L M N D .(_ => _) (exec x ())

claim3a : ∀ L M -> L ≠ M -> nonsense (Execute (Program L) (Platform M))
claim3a L .L x .(ReqN => ProN) (exec prog plat) = x Refl
claim3b : ∀ L M N -> L ≠ M -> nonsense (Execute (Interpreter L N) (Platform M))
claim3b L .L N x .(ReqN => ProY N) (exec intr plat) = x Refl
claim3c : ∀ L M N O -> L ≠ M -> nonsense (Execute (Compiler L N O) (Platform M))
claim3c L .L N O x .(ReqN => ProC N O) (exec cmpr plat) = x Refl
claim3d : ∀ K L M -> L ≠ M -> nonsense (Execute (Program L) (Interpreter K M))
claim3d K L .L x .(ReqY K => ProN) (exec prog intr) = x Refl
claim3e : ∀ K L M N -> L ≠ M -> nonsense (Execute (Interpreter L N) (Interpreter K M))
claim3e K L .L N x .(ReqY K => ProY N) (exec intr intr) = x Refl
claim3f : ∀ K L M N O -> L ≠ M -> nonsense (Execute (Compiler L N O) (Interpreter K M))
claim3f K L .L N O x .(ReqY K => ProC N O) (exec cmpr intr) = x Refl

claim4 : ∀ L D -> nonsense (Compile (Platform L) D)
claim4 L D .(ReqY _ => _) (comp () x₁)

claim5a : ∀ L D -> nonsense (Compile D (Program L))
claim5a L D .(_ => _) (comp x ())
claim5b : ∀ L M D -> nonsense (Compile D (Interpreter L M))
claim5b L M D .(_ => _) (comp x ())

claim6a : ∀ K L M N -> L ≠ M -> nonsense (Compile (Program L) (Compiler K M N))
claim6a K L .L N x .(ReqY N => ProN) (comp prog cmpr) = x Refl
claim6b : ∀ K L M N O -> L ≠ M -> nonsense (Compile (Interpreter L O) (Compiler K M N))
claim6b K L .L N O x .(ReqY N => ProY O) (comp intr cmpr) = x Refl
claim6c : ∀ K L M N O P -> L ≠ M -> nonsense (Compile (Compiler L O P) (Compiler K M N))
claim6c K L .L N O P x .(ReqY N => ProC O P) (comp cmpr cmpr) = x Refl

-- Show that the type relation is decidable by giving a type checking function

-- Note that we could also just give TypeErr always, so we have typecheckComplete
-- on the other hand, soundness is expressed by the type of TypeOK
data TypeChecked (D : Diagram) : Set where
    TypeOK : ∀ T -> D :: T -> TypeChecked D
    TypeErr : (∀ T -> ¬(D :: T)) -> TypeChecked D

-- Some useful lemmas

-- If a value has a type, then its subvalues have types
splitExecLeft : ∀ {T D₀ D₁} -> (Execute D₀ D₁ :: T) -> ∃ Type (_::_ D₀)
splitExecLeft {x₀ => x₁} (exec {L} x₂ x₃) = (ReqY L => x₁) , x₂
splitExecRight : ∀ {T D₀ D₁} -> (Execute D₀ D₁ :: T) -> ∃ Type (_::_ D₁)
splitExecRight {x₀ => x₁} (exec {L} x₂ x₃) = (x₀ => ProY L) , x₃
splitCompLeft : ∀ {T D₀ D₁} -> (Compile D₀ D₁ :: T) -> ∃ Type (_::_ D₀)
splitCompLeft {x₀ => x₁} (comp {L} x₂ x₃) = (ReqY L => x₁) , x₂
splitCompRight : ∀ {T D₀ D₁} -> (Compile D₀ D₁ :: T) -> ∃ Type (_::_ D₁)
splitCompRight {x₀ => x₁} (comp {L} {M} {N} {O} x₂ x₃) = (N => ProC L O) , x₃

-- Executing a platform is nonsense
execNeedsRequire : ∀ {D₀ D₁ T₀} -> D₀ :: ReqN => T₀ -> (T : Type) -> Execute D₀ D₁ :: T -> ⊥
execNeedsRequire {D₀} x .(_ => _) (exec x' _) with typeUnique D₀ x x'
... | ()
-- Executing on a program is nonsense
execNeedsProvide : ∀ {D₀ D₁ T₀} -> D₁ :: T₀ => ProN -> (T : Type) -> Execute D₀ D₁ :: T -> ⊥
execNeedsProvide {_} {D₁} x .(_ => _) (exec _ x') with typeUnique D₁ x x'
... | ()
-- Executing on a compiler is nonsense
execNeedsProvideY : ∀ {D₀ D₁ T₀ L M} -> D₁ :: T₀ => ProC L M -> (T : Type) -> Execute D₀ D₁ :: T -> ⊥
execNeedsProvideY {_} {D₁} x .(_ => _) (exec _ x') with typeUnique D₁ x x'
... | ()
-- Executing on a nonmatching platform or interpreter is nonsense
execCorresponding : ∀{D₀ D₁ T₀ T₁ L M} -> L ≠ M -> D₀ :: ReqY L => T₀ -> D₁ :: T₁ => ProY M -> (T : Type) → Execute D₀ D₁ :: T → ⊥
execCorresponding {D₀} {D₁} p x₀ x₁ T (exec x₀' x₁') with typeUnique D₀ x₀ x₀' | typeUnique D₁ x₁ x₁'
... | Refl | Refl = p Refl

-- Compiling a platform is nonsense
compileNeedsRequire : ∀ {D₀ D₁ T₀} -> D₀ :: ReqN => T₀ -> (T : Type) -> Compile D₀ D₁ :: T -> ⊥
compileNeedsRequire {D₀} x .(_ => _) (comp x' _) with typeUnique D₀ x x'
... | ()
-- Compiling with a program is nonsense
compileNeedsProvide : ∀ {D₀ D₁ T₀} -> D₁ :: T₀ => ProN -> (T : Type) -> Compile D₀ D₁ :: T -> ⊥
compileNeedsProvide {_} {D₁} x .(_ => _) (comp _ x') with typeUnique D₁ x x'
... | ()
-- Compiling with a platform or interpreter is nonsense
compileNeedsProvideC : ∀ {D₀ D₁ T₀ N} -> D₁ :: T₀ => ProY N -> (T : Type) -> Compile D₀ D₁ :: T -> ⊥
compileNeedsProvideC {_} {D₁} x .(_ => _) (comp _ x') with typeUnique D₁ x x'
... | ()
-- Compiling with an incompatible source language is nonsense
compileCorresponding : ∀{D₀ D₁ T₀ T₁ L M N} -> L ≠ M -> D₀ :: ReqY L => T₀ -> D₁ :: T₁ => ProC M N -> (T : Type) → Compile D₀ D₁ :: T → ⊥
compileCorresponding {D₀} {D₁} p x₀ x₁ T (comp x₀' x₁') with typeUnique D₀ x₀ x₀' | typeUnique D₁ x₁ x₁'
... | Refl | Refl = p Refl

-- The type checking function.
typecheck : (D : Diagram) -> TypeChecked D
typecheck (Program L) = TypeOK (ReqY L => ProN) prog
typecheck (Platform L) = TypeOK (ReqN => ProY L) plat
typecheck (Interpreter L M) = TypeOK (ReqY L => ProY M) intr
typecheck (Compiler L M N) = TypeOK (ReqY L => ProC M N) cmpr
typecheck (Execute D₀ D₁) with typecheck D₀ | typecheck D₁
typecheck (Execute D₀ D₁) | _ | TypeErr p = TypeErr (λ t x → choice p (splitExecRight x))
typecheck (Execute D₀ D₁) | TypeErr p | _ = TypeErr (λ t x → choice p (splitExecLeft x))
typecheck (Execute D₀ D₁) | TypeOK (ReqN => x₁) x₂ | (TypeOK (x₃ => x₄) x₅) = TypeErr (execNeedsRequire x₂)
typecheck (Execute D₀ D₁) | TypeOK (ReqY L => x₁) x₂ | (TypeOK (x₃ => ProN) x₅) = TypeErr (execNeedsProvide x₅)
typecheck (Execute D₀ D₁) | TypeOK (ReqY L => x₁) x₂ | (TypeOK (x₃ => ProY M) x₅) with L == M
typecheck (Execute D₀ D₁) | TypeOK (ReqY L => x₁) x₂ | (TypeOK (x₃ => ProY M) x₅) | (No p) = TypeErr (execCorresponding p x₂ x₅)
typecheck (Execute D₀ D₁) | TypeOK (ReqY L => x₁) x₂ | (TypeOK (x₃ => ProY .L) x₅) | (Yes Refl) = TypeOK (x₃ => x₁) (exec x₂ x₅)
typecheck (Execute D₀ D₁) | TypeOK (ReqY L => x₁) x₂ | (TypeOK (x₃ => ProC L₁ M) x₅) = TypeErr (execNeedsProvideY x₅)
typecheck (Compile D₀ D₁) with typecheck D₀ | typecheck D₁
typecheck (Compile D₀ D₁) | _ | TypeErr p = TypeErr (λ t x -> choice p (splitCompRight x))
typecheck (Compile D₀ D₁) | TypeErr p | _ = TypeErr (λ t x -> choice p (splitCompLeft x))
typecheck (Compile D₀ D₁) | TypeOK (ReqN => x₁) x₀ | (TypeOK (x₂ => x₃) x₄) = TypeErr (compileNeedsRequire x₀)
typecheck (Compile D₀ D₁) | TypeOK (ReqY L => x₁) x₀ | (TypeOK (x₂ => ProN) x₄) = TypeErr (compileNeedsProvide x₄)
typecheck (Compile D₀ D₁) | TypeOK (ReqY L => x₁) x₀ | (TypeOK (x₂ => ProY L₁) x₄) = TypeErr (compileNeedsProvideC x₄)
typecheck (Compile D₀ D₁) | TypeOK (ReqY L => x₁) x₀ | (TypeOK (x₂ => ProC M N) x₄) with L == M
typecheck (Compile D₀ D₁) | TypeOK (ReqY L => x₁) x₀ | (TypeOK (x₂ => ProC M N) x₄) | (No p) = TypeErr (compileCorresponding p x₀ x₄)
typecheck (Compile D₀ D₁) | TypeOK (ReqY L => x₁) x₀ | (TypeOK (x₂ => ProC .L N) x₄) | (Yes Refl) = TypeOK (ReqY N => x₁) (comp x₀ x₄)
