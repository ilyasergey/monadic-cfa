GHC=ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances

active: CFA MonadCFASP MonadCFASPT MonadCFASPTCh XCFA

all: MonadCFA MonadKCFA MonadCFASP CFA


XCFA: XCFA.hs
	$(GHC) --make XCFA

MonadCFASPTCh: MonadCFASPTCh.hs
	$(GHC) --make MonadCFASPTCh

MonadCFASPT: MonadCFASPT.hs
	$(GHC) --make MonadCFASPT

MonadCFASP: MonadCFASP.hs
	$(GHC) --make MonadCFASP



MonadKCFA: MonadKCFA.hs
	ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators --make MonadKCFA.hs

MonadCFA: MonadCFA.hs
	ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators --make MonadCFA


CFA: CFA.hs
	ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators --make CFA

clean:
	rm -fv *.{o,hi} MonadCFA CFA MonadKCFA MonadCFASP MonadCFASPT MonadCFASPTCh XCFA

