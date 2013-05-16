package bluemold.alg.btree

import annotation.tailrec

object BTree {
  val maxNode = 4
  val halfNode = maxNode / 2

  def zipHeadWithTail[T]( list: List[T]) = zipHeadWithTail0( list, Nil )
  @tailrec private def zipHeadWithTail0[T]( list: List[T], acc: List[(T,List[T])] ): List[(T,List[T])] = {
    val head::tail = list
    if ( tail.isEmpty ) ((head,tail)::acc).reverse
    else zipHeadWithTail0( tail, (head,tail)::acc )
  }

  def empty[K <: Comparable[K],V]: BTree[K,V] = Leaf[K,V](Nil)
}
abstract class BTree[K <: Comparable[K],V] {
  import BTree._
  def isEmpty = this.isInstanceOf[Leaf[K,V]] && nodeSize == 0
  private[btree] def isFull = nodeSize == maxNode
  private[btree] def isTooSmall = nodeSize < halfNode
  private[btree] def isTooBig = nodeSize > maxNode
  private[btree] def split(): (BTree[K,V],(K,V,BTree[K,V]))
  private[btree] def nodeSize: Int
  private[btree] def getChildNodes: List[BTree[K,V]]
  def size = size0( nodeSize, List(getChildNodes) )
  def empty = BTree.empty[K,V]
  def contains( key: K ) = contains0( key, this )
  def get( key: K ) = get0( key, this )
  def update( key: K, value: V ) = update0( key, value, this, Nil )
  def insert( key: K, value: V ) = insert0( key, value, this, Nil )
  def remove( key: K ) = remove0( key, this, Nil )
  def put( key: K, value: V ) =
    if ( contains( key ) )
      update( key, value )
    else
      insert( key, value )
  
  @tailrec private def size0( acc: Int, stack: List[List[BTree[K,V]]]): Int =
    if ( stack.isEmpty ) acc
    else {
      val level::tail = stack
      val node::rest = level
      val children = node.getChildNodes
      val newAcc = acc + node.nodeSize
      if ( children.isEmpty )
        if ( rest.isEmpty ) size0( newAcc, tail )
        else size0( newAcc, rest :: tail )
      else if ( rest.isEmpty ) size0( newAcc, children :: tail )
      else size0( newAcc, children :: rest :: tail )
    }

  @tailrec private def contains0( key: K, node: BTree[K,V] ): Boolean = node match {
    case leaf: Leaf[K,V] => leaf owns key
    case branch: Branch[K,V] =>
      if ( branch isAfter key )
        contains0( key, branch.before )
      else if ( branch owns key ) true
      else contains0( key, branch childFor key )
  }

  @tailrec private def get0( key: K, node: BTree[K,V] ): Option[V] = node match {
    case leaf: Leaf[K,V] => leaf getHere key
    case branch: Branch[K,V] =>
      if ( branch isAfter key )
        get0( key, branch.before )
      else branch getHere key match {
        case v: Some[V] => v
        case None => get0( key, branch childFor key )
      }
  }

  @tailrec private def updateHistory( o: BTree[K,V], n: BTree[K,V], history: List[Branch[K,V]] ): BTree[K,V] =
    if ( history.isEmpty ) n else updateHistory( history.head, history.head.updateNode(o,n), history.tail )

  @tailrec private def originalRoot( node: BTree[K,V], history: List[Branch[K,V]] ): BTree[K,V] =
    if ( history.isEmpty ) node else originalRoot( history.head, history.tail )

  @tailrec private def update0( key: K, value: V, node: BTree[K,V], history: List[Branch[K,V]] ): BTree[K,V] = node match {
    case leaf: Leaf[K,V] =>
      if ( leaf owns key ) updateHistory( leaf, leaf.updateHere( key, value ), history )
      else originalRoot( node, history )
    case branch: Branch[K,V] =>
      if ( branch isAfter key )
        update0( key, value, branch.before, branch :: history )
      else if ( branch owns key )
        updateHistory( branch, branch.updateHere( key, value ), history )
      else 
        update0( key, value, branch childFor key, branch :: history )
  }

  @tailrec private def insert0( key: K, value: V, node: BTree[K,V], history: List[Branch[K,V]] ): BTree[K,V] = node match {
    case leaf: Leaf[K,V] =>
      if ( leaf owns key ) originalRoot( node, history )
      else if ( !leaf.isFull ) updateHistory( leaf, leaf.insertHere( key, value ), history )
      else {
        val (left,upEntry) = leaf.insertAndSplit(key,value)
        if ( history.isEmpty ) 
          Branch[K,V](left,upEntry::Nil)
        else
          insertSplit( leaf, left, upEntry, history )
      }
    case branch: Branch[K,V] =>
      if ( branch isAfter key )
        insert0( key, value, branch.before, branch :: history )
      else if ( branch owns key )
        originalRoot( node, history )
      else 
        insert0( key, value, branch childFor key, branch :: history )
  }

  @tailrec private def insertSplit( o: BTree[K,V], n: BTree[K,V], entry: (K,V,BTree[K,V]), history: List[Branch[K,V]] ): BTree[K,V] = {
    if ( history.isEmpty ) Branch[K,V](n,entry::Nil)
    else {
      val node::moreHistory = history
      if ( node.isFull ) {
        val (left,upEntry) = node.updateInsertAndSplit(o,n,entry)
        insertSplit( node, left, upEntry, moreHistory )
      } else node.updateAndInsert(o,n,entry)
    }
  }

  private def parentIsSingle( merged: BTree[K,V], parentHistory: List[Branch[K,V]] ) = 
    if ( ! parentHistory.isEmpty ) throw new RuntimeException("!")
    else if ( merged.isTooBig ) {
      val (newLeft,upEntry) = merged.split()
      Branch[K,V]( newLeft, upEntry :: Nil )
    }
    else merged
  private def mergedIsTooBig( key: K, left: BTree[K,V], merged: BTree[K,V], branch: Branch[K,V], history: List[Branch[K,V]] ) = {
    val (newLeft,upEntry) = merged.split()
    val newBranch = branch.removeHere(key,left,newLeft).insertHere(upEntry)
    updateHistory( branch, newBranch, history )
  }
  @tailrec private def remove0( key: K, node: BTree[K,V], history: List[Branch[K,V]] ): BTree[K,V] = node match {
    case leaf: Leaf[K,V] =>
      if ( !(leaf owns key) ) originalRoot( node, history )
      else {
        val newLeaf = leaf.removeHere(key)
        if ( history.isEmpty ) newLeaf 
        else if ( ! newLeaf.isTooSmall ) updateHistory( leaf, newLeaf, history )
        else {
          val parent::parentHistory = history
          val (leafKey, left, merged ) =
            if ( parent.before eq leaf ) {
              val leafKey = parent.firstKey
              val leafValue = parent.getHere(leafKey).get
              val right = parent.childFor(leafKey).asInstanceOf[Leaf[K,V]]
              ( leafKey, leaf, Leaf[K,V]( newLeaf.entries ::: (leafKey,leafValue) :: right.entries ) )
            } else {
              val (leafKey,leafValue,_) = parent.entryForChild(leaf)
              val (left,_) = parent.getLeftRight(leafKey).asInstanceOf[(Leaf[K,V],Leaf[K,V])]
              ( leafKey, left, Leaf[K,V]( left.entries ::: (leafKey,leafValue) :: newLeaf.entries ) )
            }
          if ( parent.isSingle ) parentIsSingle( merged, parentHistory )
          else if ( merged.isTooBig ) mergedIsTooBig( leafKey, left, merged, parent, parentHistory )
          else pullDown( parent, parent.removeHere( leafKey, left, merged ), parentHistory )
        }
      }
    case branch: Branch[K,V] =>
      if ( branch isAfter key )
        remove0( key, branch.before, branch :: history )
      else if ( branch owns key ) {
        val (left,right) = branch.getLeftRight(key)
        val merged = left match {
          case left: Leaf[K,V] => right match {
            case right: Leaf[K,V] => Leaf[K,V]( left.entries ::: right.entries )
            case _: Branch[K,V] => throw new RuntimeException("!")
          }
          case left: Branch[K,V] => right match {
            case right: Branch[K,V] => merge( left, right )
            case _: Leaf[K,V] => throw new RuntimeException("!")
          }
        }
        if ( merged.isTooBig ) mergedIsTooBig( key, left, merged, branch, history ) 
        else pullDown( branch, branch.removeHere(key,left,merged), history )
      }
      else remove0( key, branch childFor key, branch :: history )
  }
  private def merge( left: Branch[K,V], right: Branch[K,V] ): Branch[K,V] = mergeDown( left, right, Nil )
  @tailrec private def mergeDown( left: Branch[K,V], right: Branch[K,V], stack: List[(Branch[K,V],Branch[K,V])] ): Branch[K,V] = {
    left.lastChild match {
      case l: Leaf[K,V] => right.before match {
        case r: Leaf[K,V] => mergeUp( left, right, stack, Leaf[K,V]( l.entries ::: r.entries ) )
        case _:Branch[K,V] => throw new RuntimeException("!")
      }
      case l: Branch[K,V] => right.before match {
        case r: Branch[K,V] => mergeDown( l, r, ((left,right))::stack )
        case _:Leaf[K,V] => throw new RuntimeException("!")
      }
    }
  }
  @tailrec private def mergeUp( left: Branch[K,V], right: Branch[K,V], stack: List[(Branch[K,V],Branch[K,V])], middleChild: BTree[K,V] ): Branch[K,V] = {
    val combine =
      if ( middleChild.isTooBig ) {
        val (newMiddleChild,upEntry) = middleChild.split()
        Branch[K,V]( left.before, left.updateChild(left.lastChild,newMiddleChild,left.entries,Nil) ::: upEntry :: right.entries )
      } else Branch[K,V]( left.before, left.updateChild(left.lastChild,middleChild,left.entries,Nil) ::: right.entries )
    if ( stack.isEmpty ) combine
    else mergeUp( stack.head._1, stack.head._2, stack.tail, combine )
  }
  @tailrec private def pullDown( o: Branch[K,V], n: Branch[K,V], history: List[Branch[K,V]] ): BTree[K,V] =
    if ( ! n.isTooSmall ) updateHistory(o,n,history)
    else if ( history.isEmpty ) n
    else {
      val parent::parentHistory = history
      val (key,left,merged) =
        if ( parent.before eq o ) {
          val key = parent.firstKey
          val child = parent.childFor(key).asInstanceOf[Branch[K,V]]
          val value = parent.getHere(key).get
          ( key, o, Branch[K,V]( n.before, n.entries ::: (key,value,child.before) :: child.entries ) )
        } else {
          val (key,value,_) = parent.entryForChild( o )
          val (left,_) = parent.getLeftRight( key ).asInstanceOf[(Branch[K,V],Branch[K,V])]
          ( key, left, Branch[K,V]( left.before, left.entries ::: (key,value,n.before) :: n.entries ) )
        }
      if ( parent.isSingle ) parentIsSingle( merged, parentHistory )
      else if ( merged.isTooBig ) mergedIsTooBig( key, left, merged, parent, parentHistory ) 
      else pullDown( parent, parent.removeHere(key,left,merged), history )
    }
}
case class Leaf[K <: Comparable[K],V]( entries: List[(K,V)]) extends BTree[K,V] {
  import BTree._
  override private[btree] def nodeSize = entries.size
  override private[btree] def getChildNodes: List[BTree[K,V]] = Nil
  override private[btree] def split() = {
    val (left,splitter::right) = entries.splitAt(entries.size/2)
    (Leaf[K,V](left),(splitter._1,splitter._2,Leaf[K,V](right)))
  }
  @tailrec private def updateEntry( key: K, value: V, entries: List[(K,V)], prior: List[(K,V)] ): List[(K,V)] =
    if ( entries.isEmpty ) prior.reverse
    else {
      val head::tail = entries
      if ( head._1.compareTo(key) == 0 ) prior reverse_::: head.copy( _2 = value ) :: tail
      else updateEntry( key, value, tail, head :: prior )
    }
  @tailrec private def insertEntry( entry: (K,V), entries: List[(K,V)], prior: List[(K,V)] ): List[(K,V)] =
    if ( entries.isEmpty ) prior reverse_::: entry :: Nil
    else {
      val head::tail = entries
      if ( head._1.compareTo(entry._1) > 0 ) prior reverse_::: entry :: entries
      else insertEntry( entry, tail, head :: prior )
    }
  @tailrec private def removeEntry( key: K, entries: List[(K,V)], prior: List[(K,V)] ) : List[(K,V)] =
    if ( entries.isEmpty ) prior.reverse
    else {
      val head::tail = entries
      if ( head._1.compareTo(key) == 0 ) prior reverse_::: tail
      else removeEntry( key, tail, head :: prior )
    }
  private[btree] def owns( key: K ) = !(entries forall { _._1.compareTo(key) != 0 })
  private[btree] def getHere( key: K ) = entries find { _._1.compareTo( key ) == 0 } map { _._2 }
  private[btree] def updateHere( key: K, value: V ) = Leaf[K,V]( updateEntry( key, value, entries, Nil ) )
  private[btree] def insertHere( entry: (K,V) ) = Leaf[K,V]( insertEntry( entry: (K,V), entries, Nil ) )
  private[btree] def insertAndSplit( entry: (K,V) ): (Leaf[K,V],(K,V,Leaf[K,V])) = {
    val (left,splitter::right) = insertEntry( entry, entries, Nil ).splitAt(halfNode)
    (Leaf[K,V](left),(splitter._1,splitter._2,Leaf[K,V](right)))
  }
  private[btree] def removeHere( key: K ) = Leaf[K,V]( removeEntry( key, entries, Nil ) )
}
case class Branch[K <: Comparable[K],V]( before: BTree[K,V], entries: List[(K,V,BTree[K,V])]) extends BTree[K,V] {
  import BTree._
  override private[btree] def nodeSize = entries.size
  override private[btree] def getChildNodes: List[BTree[K,V]] = before :: ( entries map { _._3 } )
  override private[btree] def split() = {
    val (left,splitter::right) = entries.splitAt(entries.size/2)
    (Branch[K,V](before,left),(splitter._1,splitter._2,Branch[K,V](splitter._3,right)))
  }
  private[btree] def firstKey = entries.head._1
  private[btree] def isSingle = entries.size == 1
  private[btree] def isAfter( key: K ) = firstKey.compareTo(key) > 0
  private[btree] def entryForChild( node: BTree[K,V] ) = (entries find { _._3 eq node }).get
  private[btree] def childFor( key: K ) =
    (zipHeadWithTail(entries) find { e =>
      val (_, tail) = e
      (tail.isEmpty || tail.head._1.compareTo(key) > 0)
    }).get._1._3
  private[btree] def lastChild = entries.last._3
  @tailrec private[btree] final def updateChild( o: BTree[K,V], n: BTree[K,V], entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ): List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty )
      throw new RuntimeException("!")
    else {
      val head::tail = entries
      if ( head._3 eq o )
        prior reverse_::: head.copy( _3 = n ) :: tail
      else updateChild( o, n, tail, head :: prior )
    }
  private[btree] def updateNode( o: BTree[K,V], n: BTree[K,V] ) =
    if ( before eq o ) Branch[K,V]( n, entries)
    else Branch[K,V]( before, updateChild( o, n, entries, Nil ) ) 
  @tailrec private def updateEntry( key: K, value: V, entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ): List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty )
      throw new RuntimeException("!")
    else {
      val head::tail = entries
      if ( head._1.compareTo(key) == 0 ) prior reverse_::: head.copy( _2 = value ) :: tail
      else updateEntry( key, value, tail, head :: prior )
    }
  @tailrec private def insertEntry( entry: (K,V,BTree[K,V]), entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ): List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty ) prior reverse_::: entry :: Nil
    else {
      val head::tail = entries
      if ( head._1.compareTo(entry._1) > 0 ) prior reverse_::: entry :: entries
      else insertEntry( entry, tail, head :: prior )
    }
  @tailrec private def removeEntry( key: K, entries: List[(K,V,BTree[K,V])], prior: List[(K,V,BTree[K,V])] ) : List[(K,V,BTree[K,V])] =
    if ( entries.isEmpty ) prior.reverse
    else {
      val head::tail = entries
      if ( head._1.compareTo(key) == 0 ) prior reverse_::: tail
      else removeEntry( key, tail, head :: prior )
    }
  private[btree] def getLeftRight( key: K ): (BTree[K,V],BTree[K,V]) = getLeftRight( key, before, entries )
  @tailrec private def getLeftRight( key: K, left: BTree[K,V], entries: List[(K,V,BTree[K,V])] ): (BTree[K,V],BTree[K,V]) =
    if ( entries.isEmpty ) throw new RuntimeException("!")
    else {
      val head::tail = entries
      if ( head._1.compareTo(key) == 0 ) ((left,head._3))
      else getLeftRight( key, head._3, tail )
    }
  private[btree] def owns( key: K ) = !(entries forall { _._1.compareTo(key) != 0 })
  private[btree] def getHere( key: K ) = entries find { _._1.compareTo( key ) == 0 } map { _._2 }
  private[btree] def updateHere( key: K, value: V ) = Branch[K,V]( before, updateEntry( key, value, entries, Nil ) )
  private[btree] def insertHere( entry: (K,V,BTree[K,V]) ) = Branch[K,V]( before, insertEntry( entry, entries, Nil ) )
  private[btree] def updateAndInsert( o: BTree[K,V], n: BTree[K,V], entry: (K,V,BTree[K,V]) ) = {
    val uBefore = if ( before eq o ) n else before
    val uEntries = if ( before eq o ) entries else updateChild( o, n, entries, Nil ) 
    Branch[K,V](uBefore,insertEntry( entry, uEntries, Nil ))
  }
  private[btree] def updateInsertAndSplit( o: BTree[K,V], n: BTree[K,V], entry: (K,V,BTree[K,V]) ) = {
    val uBefore = if ( before eq o ) n else before
    val uEntries = if ( before eq o ) entries else updateChild( o, n, entries, Nil ) 
    val (left,splitter::right) = insertEntry( entry, uEntries, Nil ).splitAt(halfNode)
    (Branch[K,V](uBefore,left),(splitter._1,splitter._2,Branch[K,V](splitter._3,right)))
  }
  private[btree] def removeHere( key: K, o: BTree[K,V], n: BTree[K,V] ) =
    if ( firstKey.compareTo(key) == 0 )
      Branch[K,V]( n, removeEntry( key, entries, Nil ) )
    else                                                                                             
      Branch[K,V]( before, removeEntry( key, updateChild( o, n, entries, Nil ), Nil ) )
}


