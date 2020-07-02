// See LICENSE for license details.

package firrtl.analyses

import scala.collection.mutable
import firrtl._
import firrtl.ir._
import firrtl.graph._
import firrtl.Utils._
import firrtl.annotations.TargetToken
import firrtl.traversals.Foreachers._
import firrtl.annotations.TargetToken._


/** A class representing the instance hierarchy of a working IR Circuit
  *
  * @constructor constructs an instance graph from a Circuit
  * @param c the Circuit to analyze
  */
class InstanceGraph(c: Circuit) {
  import InstanceGraph._

  /** maps module names to the DefModule node */
  val moduleMap: Map[String, ir.DefModule] = c.modules.map({m => (m.name,m) }).toMap

  private val childInstances: mutable.LinkedHashMap[String, Seq[Key]] =
    new mutable.LinkedHashMap[String, Seq[Key]] ++ c.modules.map { m => m.name -> collectInstances(m) }
  private val instantiated = childInstances.flatMap(_._2).map(_.module).toSet
  private val roots = c.modules.map(_.name).filterNot(instantiated)
  private val circuitTopInstance = topKey(c.main)

  /** A directed graph showing the instance dependencies among modules
    * in the circuit. Every (name, module) instance of a module has an edge to
    * every (name, module) instance arising from every instance statement in
    * that module.
    */
  val instanceGraph: DiGraph[Key] = buildGraph(childInstances, roots)

  // cache vertices to speed up repeat calls to findInstancesInHierarchy
  private lazy val vertices = instanceGraph.getVertices

  // This class used to be based on a DiGraph[WDefInstance] instead of DiGraph[Key].
  // For backwards compatibility, we need to transform between Key and WDefInstance.
  private def toDefInstance(k: Key): WDefInstance = WDefInstance(NoInfo, name=k.name,  module=k.module, tpe=UnknownType)
  private def toKey(d: WDefInstance): Key = Key(name=d.name, module=d.module)

  /** A directed graph showing the instance dependencies among modules
    * in the circuit. Every WDefInstance of a module has an edge to
    * every WDefInstance arising from every instance statement in
    * that module.
    */
  @deprecated("Use instanceGraph instead.", "1.4")
  lazy val graph = instanceGraph.transformNodes(toDefInstance)

  /** A list of absolute paths (each represented by a Seq of instances)
    * of all module instances in the Circuit.
    */
  @deprecated("Use fullHierarchyKey instead.", "1.4")
  lazy val fullHierarchy: mutable.LinkedHashMap[WDefInstance,Seq[Seq[WDefInstance]]] =
    graph.pathsInDAG(toDefInstance(circuitTopInstance))

  /** A list of absolute paths (each represented by a Seq of instances)
    * of all module instances in the Circuit.
    */
  private lazy val fullHierarchyKey = instanceGraph.pathsInDAG(circuitTopInstance)


  /** A count of the *static* number of instances of each module. For any module other than the top (main) module, this is
    * equivalent to the number of inst statements in the circuit instantiating each module, irrespective of the number
    * of times (if any) the enclosing module appears in the hierarchy. Note that top module of the circuit has an
    * associated count of one, even though it is never directly instantiated. Any modules *not* instantiated at all will
    * have a count of zero.
    */
  lazy val staticInstanceCount: Map[OfModule, Int] = {
    val foo = mutable.LinkedHashMap.empty[OfModule, Int]
    childInstances.keys.foreach {
      case main if main == c.main => foo += main.OfModule  -> 1
      case other                  => foo += other.OfModule -> 0
    }
    childInstances.values.flatten.map(_.OfModule).foreach {
      mod => foo += mod -> (foo(mod) + 1)
    }
    foo.toMap
  }

  /** Finds the absolute paths (each represented by a Seq of instances
    * representing the chain of hierarchy) of all instances of a particular
    * module. Note that this includes one implicit instance of the top (main)
    * module of the circuit. If the module is not instantiated within the
    * hierarchy of the top module of the circuit, it will return Nil.
    *
    * @param module the name of the selected module
    * @return a Seq[ Seq[WDefInstance] ] of absolute instance paths
    */
  @deprecated("Use findInstancesInHierarchyKey instead.", "1.4")
  def findInstancesInHierarchy(module: String): Seq[Seq[WDefInstance]] =
    findInstancesInHierarchyKey(module).map(_.map(toDefInstance))

  /** Finds the absolute paths (each represented by a Seq of instances
    * representing the chain of hierarchy) of all instances of a particular
    * module. Note that this includes one implicit instance of the top (main)
    * module of the circuit. If the module is not instantiated within the
    * hierarchy of the top module of the circuit, it will return Nil.
    *
    * @param module the name of the selected module
    * @return a Seq[ Seq[WDefInstance] ] of absolute instance paths
    */
  def findInstancesInHierarchyKey(module: String): Seq[Seq[Key]] = {
    val instances = vertices.filter(_.module == module).toSeq
    instances flatMap { i => fullHierarchyKey.getOrElse(i, Nil) }
  }

  /** An [[firrtl.graph.EulerTour EulerTour]] representation of the [[firrtl.graph.DiGraph DiGraph]] */
  lazy val tour = EulerTour(graph, toDefInstance(circuitTopInstance))

  /** Finds the lowest common ancestor instances for two module names in
    * a design
    */
  def lowestCommonAncestor(moduleA: Seq[WDefInstance],
                           moduleB: Seq[WDefInstance]): Seq[WDefInstance] = {
    tour.rmq(moduleA, moduleB)
  }

  /**
    * Module order from highest module to leaf module
    * @return sequence of modules in order from top to leaf
    */
  def moduleOrder: Seq[DefModule] = {
    instanceGraph.transformNodes(_.module).linearize.map(moduleMap(_))
  }

  private def asLinkedSet[V](s: Seq[V]): mutable.LinkedHashSet[V] = new mutable.LinkedHashSet[V]() ++ s

  /** Given a circuit, returns a map from module name to children
     * instance/module definitions
     */
  def getChildrenInstances: mutable.LinkedHashMap[String, mutable.LinkedHashSet[WDefInstance]] =
    childInstances.map{case (k,v) => k -> asLinkedSet(v.map(toDefInstance))}

  /** Given a circuit, returns a map from module name to children
    * instance/module [[firrtl.annotations.TargetToken]]s
    */
  def getChildrenInstanceOfModule: mutable.LinkedHashMap[String, mutable.LinkedHashSet[(Instance, OfModule)]] =
    childInstances.map{ case (k, v) => k -> asLinkedSet(v.map(_.toTokens)) }

  // Transforms a TraversableOnce input into an order-preserving map
  // Iterates only once, no intermediate collections
  // Can possibly be replaced using LinkedHashMap.from(..) or better immutable map in Scala 2.13
  private def asOrderedMap[K1, K2, V](it: TraversableOnce[K1], f: (K1) => (K2, V)): collection.Map[K2, V] = {
    val lhmap = new mutable.LinkedHashMap[K2, V]
    it.foreach { lhmap += f(_) }
    lhmap
  }

  /** Given a circuit, returns a map from module name to a map
    * in turn mapping instances names to corresponding module names
    */
  def getChildrenInstanceMap: collection.Map[OfModule, collection.Map[Instance, OfModule]] =
    childInstances.map(kv => kv._1.OfModule -> asOrderedMap(kv._2, (i: Key) => i.toTokens))

  /** The set of all modules in the circuit */
  lazy val modules: collection.Set[OfModule] = vertices.map(_.OfModule)

  /** The set of all modules in the circuit reachable from the top module */
  lazy val reachableModules: collection.Set[OfModule] =
    mutable.LinkedHashSet(circuitTopInstance.OfModule) ++
      instanceGraph.reachableFrom(circuitTopInstance).map(_.OfModule)

  /** The set of all modules *not* reachable in the circuit */
  lazy val unreachableModules: collection.Set[OfModule] = modules diff reachableModules
}

object InstanceGraph {
  /** We want to only use this untyped version as key because hashing bundle types is expensive
    * @param name the name of the instance
    * @param module the name of the module that is instantiated
    */
  case class Key(name: String, module: String) {
    def Instance: Instance = TargetToken.Instance(name)
    def OfModule: OfModule = TargetToken.OfModule(module)
    def toTokens: (Instance, OfModule) = (Instance, OfModule)
  }

  /** Finds all instance definitions in a firrtl Module. */
  def collectInstances(m: ir.DefModule): Seq[Key] = m match {
    case _ : ir.ExtModule => List()
    case ir.Module(_, _, _, body) => {
      val instances = mutable.ArrayBuffer[Key]()
      def onStmt(s: ir.Statement): Unit = s match {
        case firrtl.WDefInstance(_, name, module, _) => instances += Key(name, module)
        case ir.DefInstance(_, name, module, _)  => instances += Key(name, module)
        case _: firrtl.WDefInstanceConnector =>
          firrtl.Utils.throwInternalError("Expecting WDefInstance, found a WDefInstanceConnector!")
        case other => other.foreachStmt(onStmt)
      }
      onStmt(body)
      instances
    }
  }

  private def topKey(module: String): Key = Key(module, module)

  private def buildGraph(childInstances: String => Seq[Key], roots: Iterable[String]): DiGraph[Key] = {
    val instanceGraph = new MutableDiGraph[Key]

    // iterate over all modules that are not instantiated and thus act as a root
    roots.foreach { subTop =>
      // create a root node
      val topInstance = topKey(subTop)
      // graph traversal
      val instanceQueue = new mutable.Queue[Key]
      instanceQueue.enqueue(topInstance)
      while (instanceQueue.nonEmpty) {
        val current = instanceQueue.dequeue
        instanceGraph.addVertex(current)
        for (child <- childInstances(current.module)) {
          if (!instanceGraph.contains(child)) {
            instanceQueue.enqueue(child)
            instanceGraph.addVertex(child)
          }
          instanceGraph.addEdge(current, child)
        }
      }
    }
    instanceGraph
  }

  /** Returns all WDefInstances in a Statement
    *
    * @param insts mutable datastructure to append to
    * @param s statement to descend
    * @return
    */
  @deprecated("Consider using collectInstances: ir.DefModule -> Seq[Key] instead", "1.4")
  def collectInstances(insts: mutable.Set[WDefInstance])
                      (s: Statement): Unit = s match {
    case i: WDefInstance => insts += i
    case i: DefInstance => throwInternalError("Expecting WDefInstance, found a DefInstance!")
    case i: WDefInstanceConnector => throwInternalError("Expecting WDefInstance, found a WDefInstanceConnector!")
    case _ => s.foreach(collectInstances(insts))
  }
}
