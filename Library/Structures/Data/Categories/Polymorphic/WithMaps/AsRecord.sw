
The following defines both a concrete type for categories.

\begin{spec}
spec {
  import ../WithMaps

  type Cat (O,A) = {
    objects : Set O,
    arrows : Set A,
    ident : Map (O,A),
    dom : Map (A,O),
    cod : Map (A,O),
    composable? : Set (A * A),
    compose : Map (A * A, A)
  }

  def objects cat = cat.objects
  def arrows cat = cat.arrows
  def ident cat = cat.ident
  def dom cat = cat.dom
  def cod cat = cat.cod
  def composable? cat = cat.composable?
  def compose cat = cat.compose
}
\end{spec}
