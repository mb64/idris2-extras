||| Extra monad transformers
|||
|||  - StateT (re-exported from base)
|||  - MonadError interface and ExceptT transformer
|||  - MonadReader interface and ReaderT transformer
|||  - MonadCont interface and ContT transformer
|||  - MonadIO interface: like Prelude.HasIO but not linear
|||
||| TODO: WriterT and MonadWriter, RWST transformer
module Extra.Control.MonadTrans

import public Control.Monad.Trans
import public Control.Monad.State

-- Classes

||| Like Prelude.HasIO, but it doesn't require a linear lifting, so it can be
||| used with monad transformers more easily
public export
interface Monad m => MonadIO m where
  liftIO : IO a -> m a

export
implementation MonadIO IO where
  liftIO = id

export
implementation MonadIO m => MonadIO (StateT s m) where
  liftIO x = ST $ \st => do
    val <- liftIO x
    pure (val, st)

public export
interface Monad m => MonadError e m | m where
  throwError : e -> m a
  catchError : m a -> (e -> m a) -> m a

export
implementation MonadError e (Either e) where
  throwError = Left
  catchError (Left e) f = f e
  catchError (Right x) f = Right x

export
implementation MonadError () Maybe where
  throwError () = Nothing
  catchError Nothing f = f ()
  catchError (Just x) f = Just x

export
implementation MonadError e m => MonadError e (StateT s m) where
  throwError e = lift $ throwError e
  catchError (ST x) f = ST $ \st => catchError (x st) $ flip runStateT st . f

public export
interface Monad m => MonadReader r m | m where
  ask : m r
  local : (r -> r) -> m a -> m a
  reader : (r -> a) -> m a

-- public export
-- implementation MonadReader r ((->) r) where
--   ask = id
--   local f g = g . f
--   reader = id

public export
interface Monad m => MonadCont m where
  callCC : ((a -> m b) -> m a) -> m a

export
implementation MonadCont m => MonadCont (StateT s m) where
  callCC f = ST $ \s =>
             callCC $ \c =>
             runStateT (f $ \a => ST $ \s' => c (a, s')) s
-- Which state to use?  Both s or s' make sense     ^^
-- in different situtations.  Choosing s' for now, since
-- that's what Haskell does.


-- ExceptT

public export
record ExceptT (e : Type) (m : Type -> Type) (a : Type) where
  constructor MkExceptT
  runExceptT : m (Either e a)

export
implementation Functor m => Functor (ExceptT e m) where
  map f (MkExceptT x) = MkExceptT $ map (map f) x

export
implementation Monad m => Applicative (ExceptT e m) where
  pure = MkExceptT . pure . pure

  (MkExceptT mf) <*> (MkExceptT mx) = MkExceptT $ do
    Right f <- mf
      | Left e => pure $ Left e
    Right x <- mx
      | Left e => pure $ Left e
    pure $ Right $ f x

export
implementation Monad m => Monad (ExceptT e m) where
  (MkExceptT mx) >>= f = MkExceptT $ do
    Right x <- mx
      | Left e => pure $ Left e
    runExceptT $ f x

export
implementation MonadTrans (ExceptT e) where
  lift x = MkExceptT $ map Right x

export
implementation MonadState s m => MonadState s (ExceptT e m) where
  get = lift get
  put x = lift $ put x

export
implementation Monad m => MonadError e (ExceptT e m) where
  throwError = MkExceptT . pure . Left
  catchError (MkExceptT mx) f = MkExceptT $ do
    Left e <- mx
      | Right x => pure $ Right x
    runExceptT $ f e

export
implementation MonadIO m => MonadIO (ExceptT e m) where
  liftIO = MkExceptT . map Right . liftIO

export
implementation MonadReader r m => MonadReader r (ExceptT e m) where
  ask = lift ask
  local f (MkExceptT x) = MkExceptT $ local f x
  reader = lift . reader

export
implementation MonadCont m => MonadCont (ExceptT e m) where
  callCC f = MkExceptT $
    callCC $ \cont => runExceptT $ f $ MkExceptT . cont . Right


-- ReaderT

public export
record ReaderT (r : Type) (m : Type -> Type) (a : Type) where
  constructor MkReaderT
  runReaderT : r -> m a

export
implementation Functor m => Functor (ReaderT r m) where
  map f (MkReaderT g) = MkReaderT $ map f . g

export
implementation Applicative m => Applicative (ReaderT r m) where
  pure = MkReaderT . const . pure
  MkReaderT f <*> MkReaderT x = MkReaderT $ \r => f r <*> x r

export
implementation Monad m => Monad (ReaderT r m) where
  MkReaderT x >>= f = MkReaderT $ \r => x r >>= flip runReaderT r . f

export
implementation MonadTrans (ReaderT r) where
  lift = MkReaderT . const

export
implementation Monad m => MonadReader r (ReaderT r m) where
  ask = MkReaderT pure
  local f (MkReaderT x) = MkReaderT $ x . f
  reader f = MkReaderT $ pure . f

export
implementation MonadState s m => MonadState s (ReaderT r m) where
  get = MkReaderT $ const get
  put = MkReaderT . const . put

export
implementation MonadError e m => MonadError e (ReaderT r m) where
  throwError = MkReaderT . const . throwError
  catchError (MkReaderT a) h = MkReaderT $ \r => catchError (a r) (flip runReaderT r . h)

export
implementation MonadIO m => MonadIO (ReaderT r m) where
  liftIO = MkReaderT . const . liftIO

export
implementation MonadCont m => MonadCont (ReaderT r m) where
  callCC f = MkReaderT $ \r =>
    callCC $ \cont => flip runReaderT r $ f $ lift . cont


-- ContT

public export
data ContT : (r : k) -> (m : k -> Type) -> Type -> Type where
  MkContT : ((a -> m r) -> m r) -> ContT r m a

public export
runContT : ContT r m a -> (a -> m r) -> m r
runContT (MkContT c) = c

export
implementation Functor (ContT r m) where
  map f (MkContT c) = MkContT $ c . (. f)

export
implementation Applicative (ContT r m) where
  pure x = MkContT ($ x)
  MkContT f <*> MkContT x = MkContT $ \cont => f $ x . (cont .)

export
implementation Monad (ContT r m) where
  MkContT x >>= f = MkContT $ \cont => x $ (\cx => runContT (f cx) cont)

export
implementation MonadTrans (ContT r) where
  lift x = MkContT (x >>=)

export
implementation MonadCont (ContT r m) where
  callCC f = MkContT $ \cont => runContT (f $ \fc => MkContT $ \_ => cont fc) cont

export
implementation MonadReader r' m => MonadReader r' (ContT r m) where
  ask = lift ask
  local f (MkContT x) = MkContT $ local f . x
  reader = lift . reader

export
implementation MonadState s m => MonadState s (ContT r m) where
  get = lift get
  put = lift . put

export
implementation MonadIO m => MonadIO (ContT r m) where
  liftIO = lift . liftIO
