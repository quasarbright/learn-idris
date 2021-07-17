module TypedInterpreter

import Data.Vect
import Data.Fin

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt = Integer
interpTy TyBool = Bool
interpTy (TyFun arg ret) = interpTy arg -> interpTy ret

{-
de brujin indexed lambda calculus with numbers and bools
A variable reference is written as a natural indicating how many lambdas away its binder is. (\.1) is the identity function, (\.\.2) is const, etc.
This representation makes ill-typed programs un-representable!
-}
using (ctx:Vect n Ty) -- ctx for gamma? It's the context
    -- type-level proof that (k:t) in ctx
    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
        Stop : HasType FZ (t :: ctx) t -- the first variable in the context has type t
        Pop  : HasType k ctx t -> HasType (FS k) (u :: ctx) t
        -- (k:t) somewhere in the context. Basically putting an annotation before (k:t), but (k:t) might be deep in there

    -- Expr ctx t means an expression with type t in context ctx
    -- The types in the constructors encode the type judgements
    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i ctx t -> Expr ctx t
        Val : (x : Integer) -> Expr ctx TyInt
        Lam : Expr (a :: ctx) t -> Expr ctx (TyFun a t) -- the body has ctx (a :: ctx). Pushes the argument to the body's context
        App : Expr ctx (TyFun a t) -> Expr ctx a -> Expr ctx t
        Op  : (interpTy a -> interpTy b -> interpTy c) ->
            Expr ctx a -> Expr ctx b -> Expr ctx c
        If  : Expr ctx TyBool ->
            Lazy (Expr ctx a) ->
            Lazy (Expr ctx a) -> Expr ctx a

    -- actually contains the values!
    data Env : Vect n Ty -> Type where
        Nil  : Env Nil
        (::) : interpTy a -> Env ctx -> Env (a :: ctx)
        -- takes a value of the idris type of a and adds its Ty type to the context
    
    lookup : HasType i ctx t -> Env ctx -> interpTy t
    lookup Stop (x :: xs) = x
    lookup (Pop h) (x :: xs) = lookup h xs

    interp : Env ctx -> Expr ctx t -> interpTy t
    interp e (Val n) = n
    interp e (Var v) = lookup v e
    interp e (Lam body) = \a => interp (a :: e) body
    interp e (App f x) = interp e f $ interp e x
    interp e (Op f l r) = f (interp e l) (interp e r)
    interp e (If cnd thn els) = if interp e cnd then interp e thn else interp e els


