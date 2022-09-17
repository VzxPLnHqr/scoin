package scoin

import java.nio.{ByteBuffer, ByteOrder}
import scala.language.implicitConversions
import scala.concurrent.duration.{DurationLong, FiniteDuration}
import scodec.bits.{ByteVector, ByteOrdering}

case class CltvExpiryDelta(private val underlying: Int)
    extends Ordered[CltvExpiryDelta] {
  def toCltvExpiry(height: Long): CltvExpiry = CltvExpiry(height + underlying)
  def toCltvExpiry(height: BlockHeight): CltvExpiry = toCltvExpiry(
    height.underlying
  )

  def +(height: BlockHeight): CltvExpiry = toCltvExpiry(height)
  def +(height: Long): CltvExpiry = toCltvExpiry(height)
  def +(other: Int): CltvExpiryDelta = CltvExpiryDelta(underlying + other)
  def +(other: CltvExpiryDelta): CltvExpiryDelta = CltvExpiryDelta(
    underlying + other.underlying
  )
  def -(other: CltvExpiryDelta): CltvExpiryDelta = CltvExpiryDelta(
    underlying - other.underlying
  )
  def *(m: Int): CltvExpiryDelta = CltvExpiryDelta(underlying * m)
  def compare(other: CltvExpiryDelta): Int =
    underlying.compareTo(other.underlying)
  def toInt: Int = underlying
}

case class CltvExpiry(private val underlying: BlockHeight)
    extends Ordered[CltvExpiry] {
  def +(d: CltvExpiryDelta): CltvExpiry = CltvExpiry(underlying + d.toInt)
  def -(d: CltvExpiryDelta): CltvExpiry = CltvExpiry(underlying - d.toInt)
  def -(other: CltvExpiry): CltvExpiryDelta = CltvExpiryDelta(
    (underlying - other.underlying).toInt
  )
  def -(other: BlockHeight): CltvExpiryDelta = CltvExpiryDelta(
    (underlying - other).toInt
  )
  override def compare(other: CltvExpiry): Int =
    underlying.compareTo(other.underlying)
  def blockHeight: BlockHeight = underlying
  def toLong: Long = underlying.toLong
}

object CltvExpiry {
  def apply(underlying: Int): CltvExpiry = CltvExpiry(BlockHeight(underlying))
  def apply(underlying: Long): CltvExpiry = CltvExpiry(BlockHeight(underlying))
}

case class ShortChannelId(private val id: Long)
    extends Ordered[ShortChannelId] {
  def toLong: Long = id
  def blockHeight = ShortChannelId.blockHeight(this)

  override def toString: String = {
    val TxCoordinates(blockHeight, txIndex, outputIndex) =
      ShortChannelId.coordinates(this)
    s"${blockHeight.toLong}x${txIndex}x$outputIndex"
  }

  // we use an unsigned long comparison here
  override def compare(that: ShortChannelId): Int =
    (this.id + Long.MinValue).compareTo(that.id + Long.MinValue)
}

object ShortChannelId {
  def apply(s: String): ShortChannelId = s.split("x").toList match {
    case blockHeight :: txIndex :: outputIndex :: Nil =>
      ShortChannelId(
        toShortId(blockHeight.toInt, txIndex.toInt, outputIndex.toInt)
      )
    case _ =>
      throw new IllegalArgumentException(s"Invalid short channel id: $s")
  }
  def apply(
      blockHeight: BlockHeight,
      txIndex: Int,
      outputIndex: Int
  ): ShortChannelId = ShortChannelId(
    toShortId(blockHeight.toInt, txIndex, outputIndex)
  )
  def toShortId(blockHeight: Int, txIndex: Int, outputIndex: Int): Long =
    ((blockHeight & 0xffffffL) << 40) | ((txIndex & 0xffffffL) << 16) | (outputIndex & 0xffffL)
  @inline
  def blockHeight(shortChannelId: ShortChannelId): BlockHeight = BlockHeight(
    (shortChannelId.id >> 40) & 0xffffff
  )
  @inline
  def txIndex(shortChannelId: ShortChannelId): Int =
    ((shortChannelId.id >> 16) & 0xffffff).toInt
  @inline
  def outputIndex(shortChannelId: ShortChannelId): Int =
    (shortChannelId.id & 0xffff).toInt
  def coordinates(shortChannelId: ShortChannelId): TxCoordinates =
    TxCoordinates(
      blockHeight(shortChannelId),
      txIndex(shortChannelId),
      outputIndex(shortChannelId)
    )
}

case class TxCoordinates(
    blockHeight: BlockHeight,
    txIndex: Int,
    outputIndex: Int
)

case class BlockHeight(val underlying: Long) extends Ordered[BlockHeight] {
  override def compare(other: BlockHeight): Int =
    underlying.compareTo(other.underlying)
  def +(i: Int) = BlockHeight(underlying + i)
  def +(l: Long) = BlockHeight(underlying + l)
  def -(i: Int) = BlockHeight(underlying - i)
  def -(l: Long) = BlockHeight(underlying - l)
  def -(other: BlockHeight): Long = underlying - other.underlying
  def unary_- = BlockHeight(-underlying)

  def max(other: BlockHeight): BlockHeight = if (this > other) this else other
  def min(other: BlockHeight): BlockHeight = if (this < other) this else other

  def toInt: Int = underlying.toInt
  def toLong: Long = underlying
  def toDouble: Double = underlying.toDouble
}

case class TimestampSecond(private val underlying: Long)
    extends Ordered[TimestampSecond] {
  require(
    underlying >= 0 && underlying <= 253402300799L,
    s"invalid timestamp value $underlying"
  )
  // @formatter:off
  def toLong: Long = underlying
  def toTimestampMilli: TimestampMilli = TimestampMilli(underlying * 1000)
  override def toString: String = s"$underlying unixsec"
  override def compare(that: TimestampSecond): Int = underlying.compareTo(that.underlying)
  def +(x: Long): TimestampSecond = TimestampSecond(underlying + x)
  def -(x: Long): TimestampSecond = TimestampSecond(underlying - x)
  def +(x: FiniteDuration): TimestampSecond = TimestampSecond(underlying + x.toSeconds)
  def -(x: FiniteDuration): TimestampSecond = TimestampSecond(underlying - x.toSeconds)
  def -(x: TimestampSecond): FiniteDuration = (underlying - x.underlying).seconds
  // @formatter:on
}

object TimestampSecond {
  val min: TimestampSecond = TimestampSecond(0) // 1/1/1970
  val max: TimestampSecond = TimestampSecond(253402300799L) // 31/12/9999
  def now(): TimestampSecond = TimestampSecond(
    System.currentTimeMillis() / 1000
  )
}

case class TimestampMilli(private val underlying: Long)
    extends Ordered[TimestampMilli] {
  require(
    underlying >= 0 && underlying <= 253402300799L * 1000,
    "invalid timestamp value"
  )
  def toLong: Long = underlying
  override def toString: String = s"$underlying unixms"
  override def compare(that: TimestampMilli): Int =
    underlying.compareTo(that.underlying)
  def +(x: FiniteDuration): TimestampMilli = TimestampMilli(
    underlying + x.toMillis
  )
  def -(x: FiniteDuration): TimestampMilli = TimestampMilli(
    underlying - x.toMillis
  )
  def -(x: TimestampMilli): FiniteDuration = (underlying - x.underlying).millis
}

object TimestampMilli {
  val min: TimestampMilli = TimestampMilli(0) // 1/1/1970
  val max: TimestampMilli = TimestampMilli(253402300799L * 1000) // 31/12/9999
  def now(): TimestampMilli = TimestampMilli(System.currentTimeMillis())
}
