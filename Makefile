GHC=ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances

cps: CPSConcrete CPSAbstractNonShared CPSAbstractNonSharedCount CPSAbstractShared CPSAbstractSharedCount

CPSConcrete: CFA/CPS/Examples/Concrete.hs
	$(GHC) --make CFA/CPS/Examples/Concrete.hs

CPSAbstractNonShared: CFA/CPS/Examples/AbstractNonShared.hs
	$(GHC) --make CFA/CPS/Examples/AbstractNonShared.hs

CPSAbstractNonSharedCount: CFA/CPS/Examples/AbstractNonSharedCount.hs
	$(GHC) --make CFA/CPS/Examples/AbstractNonSharedCount.hs

CPSAbstractShared: CFA/CPS/Examples/AbstractShared.hs
	$(GHC) --make CFA/CPS/Examples/AbstractShared.hs

CPSAbstractSharedCount: CFA/CPS/Examples/AbstractSharedCount.hs
	$(GHC) --make CFA/CPS/Examples/AbstractSharedCount.hs


clean:
	find . -type f -name "*.o" -exec rm -fv {} \;
	find . -type f -name "*.hi" -exec rm -fv {} \;


