package org.apache.lucene.index.values;
/**
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import java.io.IOException;

import org.apache.lucene.index.values.IndexDocValues.Source;
import org.apache.lucene.store.IndexInput;
import org.apache.lucene.util.BytesRef;

/**
 * @lucene.internal
 */
public abstract class DirectSource extends Source{

    protected final IndexInput data;
    private final ValueType type;
    private final OffsetAndSize offsetAndSize = new OffsetAndSize();
    private final ToNumeric toNumeric;
    protected final long baseOffset;

    DirectSource(IndexInput input, ValueType type) {
      this.data = input;
      this.type = type;
      baseOffset = input.getFilePointer();
      switch (type) {
      case FIXED_INTS_16:
        toNumeric = new ShortToLong();
        break;
      case FLOAT_32:
      case FIXED_INTS_32:
        toNumeric = new IntToLong();
        break;
      case FIXED_INTS_8:
        toNumeric = new ByteToLong();
        break;
      default:
        toNumeric = new LongToLong();
      }
    }

    @Override
    public BytesRef getBytes(int docID, BytesRef ref) {
      
      try {
        offsetAndSize(docID, offsetAndSize);
        data.seek(offsetAndSize.offset + baseOffset);
        ref.grow(offsetAndSize.size);
        data.readBytes(ref.bytes, 0, offsetAndSize.size);
        ref.length = offsetAndSize.size;
        ref.offset = 0;
        return ref;
      } catch (IOException ex) {
        throw new RuntimeException(ex);
      }
    }

    @Override
    public long getInt(int docID) {
      try {
        offsetAndSize(docID, offsetAndSize);
        data.seek(offsetAndSize.offset + baseOffset);
        return toNumeric.toLong(data);
      } catch (IOException ex) {
        throw new RuntimeException(ex);
      }
    }

    @Override
    public double getFloat(int docID) {
      try {
        offsetAndSize(docID, offsetAndSize);
        data.seek(offsetAndSize.offset + baseOffset);
        return toNumeric.toDouble(data);
      } catch (IOException ex) {
        throw new RuntimeException(ex);
      }
    }

    protected abstract void offsetAndSize(int docID, OffsetAndSize offsetAndSize)
        throws IOException;

    @Override
    public ValueType type() {
      return type;
    }


  public static class OffsetAndSize {
    long offset;
    int size;
  }

  private abstract static class ToNumeric {
    abstract long toLong(IndexInput input) throws IOException;

    double toDouble(IndexInput input) throws IOException {
      return toLong(input);
    }
  }

  private static final class ByteToLong extends ToNumeric {
    @Override
    long toLong(IndexInput input) throws IOException {
      return input.readByte();
    }

  }

  private static final class ShortToLong extends ToNumeric {
    @Override
    long toLong(IndexInput input) throws IOException {
      return input.readShort();
    }
  }

  private static final class IntToLong extends ToNumeric {
    @Override
    long toLong(IndexInput input) throws IOException {
      return input.readInt();
    }

    double toDouble(IndexInput input) throws IOException {
      return Float.intBitsToFloat(input.readInt());
    }
  }

  private static final class LongToLong extends ToNumeric {
    @Override
    long toLong(IndexInput input) throws IOException {
      return input.readLong();
    }

    double toDouble(IndexInput input) throws IOException {
      return Double.longBitsToDouble(input.readLong());
    }
  }

}
