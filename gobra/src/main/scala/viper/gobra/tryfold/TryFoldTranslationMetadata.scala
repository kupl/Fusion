package viper.gobra.tryfold

final case class DynamicPredicateAlternativeMetadata(
                                                      typeKey: String,
                                                      typeExprRepr: String,
                                                      trivialBody: Boolean,
                                                    )

final case class DynamicPredicateFamilyMetadata(
                                                 silverName: String,
                                                 gobraName: String,
                                                 receiverFormalName: String = "i",
                                                 receiverArgumentIndex: Int = 0,
                                                 receiverTupleTypeSlot: Int = 1,
                                                 receiverTupleArity: Int = 2,
                                                 alternatives: Vector[DynamicPredicateAlternativeMetadata] = Vector.empty,
                                               ) {
  lazy val typeExprToKey: Map[String, String] =
    alternatives.iterator.map(alt => alt.typeExprRepr -> alt.typeKey).toMap
}

final case class TryFoldTranslationMetadata(
                                             dynamicPredicateMap: Map[String, String],
                                             dynamicPredicateFamilies: Map[String, DynamicPredicateFamilyMetadata] = Map.empty,
                                           )

object TryFoldTranslationMetadata {
  val empty: TryFoldTranslationMetadata = TryFoldTranslationMetadata(Map.empty, Map.empty)
}
