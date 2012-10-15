%%% Should directly go to sets as characteristic Maps, i.e. Set a = Map(a, Bool)

SetsAsBagMaps = SetsAsBags[BagsAsMaps#M]

M = morphism Sets -> SetsAsBagMaps {Set._ +-> SetsAsBags._}