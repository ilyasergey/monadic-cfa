
all: MonadCFA MonadKCFA CFA



MonadKCFA: MonadKCFA.hs
	ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators --make MonadKCFA.hs


MonadCFA: MonadCFA.hs
	ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators --make MonadCFA


CFA: CFA.hs
	ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators --make CFA

clean:
	rm -fv *.{o,hi} MonadCFA CFA MonadKCFA

