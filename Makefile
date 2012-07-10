GHC=ghc -XTypeSynonymInstances -XParallelListComp -XTypeOperators -XMultiParamTypeClasses -XFlexibleInstances

all: cps cesk afj

# Abstract machine for Lambda calculus in CPS
cps: CPSSimple CPSConcrete CPSAbstractNonShared CPSAbstractNonSharedCount CPSAbstractShared CPSAbstractSharedCount

CPSSimple: CFA/CPS/Examples/Concrete.hs
	$(GHC) --make CFA/CPS/Analysis/SimpleAnalysis.hs

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

# CESK machine for Lambda calculus
cesk: CESKConcrete CESKAbstractNonShared

CESKConcrete: CFA/CESK/Examples/Concrete.hs
	$(GHC) --make CFA/CESK/Examples/Concrete.hs

CESKAbstractNonShared: CFA/CESK/Examples/AbstractNonShared.hs
	$(GHC) --make CFA/CESK/Examples/AbstractNonShared.hs

# CESK machine for A-Normal Featherweight Java
afj: AFJAbstractNonShared

AFJAbstractNonShared: CFA/AFJ/Examples/AbstractNonShared.hs
	$(GHC) --make CFA/AFJ/Examples/AbstractNonShared.hs


clean:
	find . -type f -name "*.o" -exec rm -fv {} \;
	find . -type f -name "*.hi" -exec rm -fv {} \;


