||| Derive Eq and DecEq
|||
||| You'll get cryptic errors if you try to use it without importing
||| `Language.Reflection` and `Extra.Prelude`.
module Extra.Language.Derive

import Extra.Prelude
import Language.Reflection
import Decidable.Equality

%language ElabReflection

argTys : (ty : TTImp) -> List TTImp
argTys (IPi _ _ ExplicitArg _ argTy retTy) = argTy :: argTys retTy
argTys (IPi _ _ _ _ _ retTy) = argTys retTy
argTys _ = []

countArgs : (ty : TTImp) -> Nat
countArgs = length . argTys

fullyBind : FC -> TTImp -> String -> Int -> (ty : TTImp) -> TTImp
fullyBind pos f argName i (IPi _ _ ExplicitArg _ _ retTy)
  = fullyBind pos (IApp pos f (IBindVar pos (argName ++ show i))) argName (i+1) retTy
fullyBind pos f argName i (IPi _ _ _ _ _ retTy)
  = fullyBind pos f argName i retTy
fullyBind pos f argName i _ = f

fullyApply : FC -> TTImp -> String -> Int -> (ty : TTImp) -> TTImp
fullyApply pos f argName i (IPi _ _ ExplicitArg _ _ retTy)
  = fullyApply pos (IApp pos f (IVar pos $ UN $ argName ++ show i)) argName (i+1) retTy
fullyApply pos f argName i (IPi _ _ _ _ _ retTy)
  = fullyApply pos f argName i retTy
fullyApply pos f argName i _ = f

lookupConstr : Name -> Elab (Name, TTImp)
lookupConstr constr = do
  [(n, ty)] <- getType constr
    | [] => fail $ "constr " ++ show constr ++ " does not exist? hmmm"
    | _ => fail $ "ambiguous name for constr " ++ show constr
  pure (n, ty)

lookupType : Name -> Elab (Name, TTImp)
lookupType typeName = do
  [(n, ty)] <- getType typeName
    | [] => fail $ "name " ++ show typeName ++ " not in scope"
    | _ => fail $ "ambiguous name " ++ show typeName
  pure (n, ty)

||| Derive `Eq` for a type.
|||
||| Use:
||| mutual
|||   myEq : Eq a => MyType a -> MyType a -> Bool
|||   %runElab deriveEq `{{ myEq }} `{{ MyType }}
|||
|||   Eq a => Eq (MyType a) where
|||     (==) = myEq
export
deriveEq : Name -> Name -> Elab ()
deriveEq funcName typeName = do
  let pos = MkFC ("deriveEq for " ++ show typeName) (0,0) (0,0)
  (n, _) <- lookupType typeName
  constrs <- getCons n
  let and : TTImp -> TTImp -> TTImp
      and x y = `(~(x) && ~(y))
      compareEq : String -> String -> TTImp
      compareEq x y = `(~(IVar pos $ UN x) == ~(IVar pos $ UN y))
      makeClause : Name -> Elab Clause
      makeClause constr = do
        (_, ty) <- lookupConstr constr
        let nArgs = countArgs ty
        let xs = map (\i => "x_" ++ show i) $ take nArgs [1..]
        let ys = map (\i => "y_" ++ show i) $ take nArgs [1..]
        let px = foldl (IApp pos) (IVar pos constr) $ map (IBindVar pos) xs
        let py = foldl (IApp pos) (IVar pos constr) $ map (IBindVar pos) ys
        pure $ PatClause pos `(MkPair ~(px) ~(py))
             $ foldl and `(True) $ zipWith compareEq xs ys
      finalClause : Clause
      finalClause = PatClause pos `(_) `(False)
  clauses <- traverse makeClause constrs
  let allClauses = clauses ++ [finalClause]
      caseExpr = ICase pos `(MkPair x y) (Implicit pos True) allClauses
      result = `(\x, y => ~(caseExpr))
      clauses = [PatClause pos (IVar pos funcName) result]
  declare [IDef pos funcName clauses]


-- Wow! what an opportunity to derive equality
mutual
  eqName : Name -> Name -> Bool
  %runElab deriveEq `{{ eqName }} `{{ Name }}

  export
  Eq Name where
    (==) = eqName


||| Derive `DecEq` for a type.
|||
||| Use:
||| mutual
|||   myDecEq : DecEq a => (x : MyType a) -> (y : MyType a) -> Dec (x = y)
|||   %runElab deriveDecEq `{{ myDecEq }} `{{ MyType }}
|||
|||   DecEq a => DecEq (MyType a) where
|||     decEq = myDecEq
export
deriveDecEq : Name -> Name -> Elab ()
deriveDecEq funcName typeName = do
  let pos = MkFC ("deriveDecEq for " ++ show typeName) (0,0) (0,0)
      thisFunc = IVar pos funcName
  (n, _) <- lookupType typeName
  constrs <- getCons n
  let makeClause : Int -> (Int -> TTImp) -> TTImp -> List TTImp -> TTImp -> Clause
      makeClause i mkIndTy lhsSoFar withBinds ty = case ty of
        IPi _ _ ExplicitArg _ argTy retTy =>
          let nArgs = 1 + countArgs retTy
              px = fullyBind pos lhsSoFar "x__" i ty
              py = fullyBind pos lhsSoFar "y__" i ty
              thisX = IVar pos $ UN $ "x__" ++ show i
              thisY = IVar pos $ UN $ "y__" ++ show i
              decEqXY = `(decEq ~(thisX) ~(thisY))
              lhs = foldl (IApp pos) `(~(thisFunc) ~(px) ~(py)) withBinds
          in WithClause pos lhs decEqXY [
            -- No clause
            PatClause pos `(~(lhs) (No ~(IBindVar pos "bad")))
              $ ILocal pos `[ ind : ~(mkIndTy i)
                              ind Refl = Refl ]
                           `(No (bad . ind)),
            -- Yes clause
            makeClause (i+1)
                       mkIndTy
                       (IApp pos lhsSoFar thisX)
                       (withBinds ++ [`(Yes Refl)])
                       retTy
            ]
        IPi _ _ _ _ _ retTy =>
          makeClause i mkIndTy lhsSoFar withBinds retTy -- Ignore implicit arguments
        _ => let startingLhs = `(~(thisFunc) ~(lhsSoFar) ~(lhsSoFar))
                 lhs = foldl (IApp pos) startingLhs withBinds
             in PatClause pos lhs `(Yes Refl)
      -- bindImplicits "x" Constr (typeof Constr) thing = forall xi. thing
      bindImplicits : String -> Name -> TTImp -> TTImp -> TTImp
      bindImplicits varName constr ty thing =
        let args = the (List (Int, _)) $ zip [1..] $ argTys ty in
        let implicitPi : (String,TTImp) -> TTImp -> TTImp
            implicitPi (n,arg) ty = IPi pos M0 ImplicitArg (Just $ UN n) arg ty
        in foldr implicitPi thing $ map (\(i,t) => (varName ++ show i, t)) args
      makeSameClause : Name -> Elab Clause
      makeSameClause constr = do
        (name, ty) <- lookupConstr constr
        let boundA = fullyApply pos (IVar pos name) "a__" 1 ty
            boundB = fullyApply pos (IVar pos name) "b__" 1 ty
        let makeIndTy : Int -> TTImp
            makeIndTy i = let a = IVar pos $ UN $ "a__" ++ show i
                              b = IVar pos $ UN $ "b__" ++ show i
                          in bindImplicits "a__" name ty
                            $ bindImplicits "b__" name ty
                            $ `(~(boundA) === ~(boundB) -> ~(a) === ~(b))
        pure $ makeClause 1 makeIndTy (IVar pos name) [] ty
      makeDiffClause : Name -> Name -> Elab Clause
      makeDiffClause c1 c2 = do
        (n1, ty1) <- lookupConstr c1
        (n2, ty2) <- lookupConstr c2
        let thing1 = fullyApply pos (IVar pos n1) "a__" 1 ty1
            thing2 = fullyApply pos (IVar pos n2) "b__" 1 ty2
            badTy = bindImplicits "a__" n1 ty1
                  $ bindImplicits "b__" n2 ty2
                  $ `(~(thing1) = ~(thing2) -> Void)
        let pat1 : TTImp
            pat1 = foldl (\t, _ => IApp pos t (Implicit pos True)) (IVar pos n1) $ argTys ty1
            pat2 : TTImp
            pat2 = foldl (\t, _ => IApp pos t (Implicit pos True)) (IVar pos n2) $ argTys ty2
            lhs : TTImp
            lhs = `(~(thisFunc) ~(pat1) ~(pat2))
            bad : List Decl
            bad = [IClaim pos MW Private [] $ MkTy pos (UN "bad") badTy]
                ++ `[ bad Refl impossible ]
        pure $ PatClause pos lhs
             $ ILocal pos bad `(No bad)
  clauses <- sequence $ do
    a <- constrs
    b <- constrs
    pure $ if a == b then makeSameClause a
                     else makeDiffClause a b
  declare [IDef pos funcName clauses]
