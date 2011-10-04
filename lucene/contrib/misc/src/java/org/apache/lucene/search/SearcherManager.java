package org.apache.lucene.search;

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
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Semaphore;

import org.apache.lucene.index.IndexReader;
import org.apache.lucene.index.IndexWriter;
import org.apache.lucene.index.NRTManager; // javadocs
import org.apache.lucene.search.IndexSearcher; // javadocs
import org.apache.lucene.store.AlreadyClosedException;
import org.apache.lucene.store.Directory;

/** Utility class to safely share {@link IndexSearcher} instances
 *  across multiple threads, while periodically reopening.
 *  This class ensures each IndexSearcher instance is not
 *  closed until it is no longer needed.
 *
 *  <p>Use {@link #acquire} to obtain the current searcher, and
 *  {@link #release} to release it, like this:
 *
 *  <pre>
 *    IndexSearcher s = manager.acquire();
 *    try {
 *      // Do searching, doc retrieval, etc. with s
 *    } finally {
 *      manager.release(s);
 *    }
 *    // Do not use s after this!
 *    s = null;
 *  </pre>
 *
 *  <p>In addition you should periodically call {@link
 *  #maybeReopen}.  While it's possible to call this just
 *  before running each query, this is discouraged since it
 *  penalizes the unlucky queries that do the reopen.  It's
 *  better to  use a separate background thread, that
 *  periodically calls maybeReopen.  Finally, be sure to
 *  call {@link #close} once you are done.
 *
 *  <p><b>NOTE</b>: if you have an {@link IndexWriter}, it's
 *  better to use {@link NRTManager} since that class pulls
 *  near-real-time readers from the IndexWriter.
 *
 *  @lucene.experimental
 */

public class SearcherManager extends SearchManager {

  private final SearcherWarmer warmer;
  private final Semaphore reopening = new Semaphore(1);
  private final ExecutorService es;

  /** Opens an initial searcher from the Directory.
   *
   * @param dir Directory to open the searcher from
   *
   * @param warmer optional {@link SearcherWarmer}.  Pass
   *        null if you don't require the searcher to warmed
   *        before going live.
   *
   *  <p><b>NOTE</b>: the provided {@link SearcherWarmer} is
   *  not invoked for the initial searcher; you should
   *  warm it yourself if necessary.
   */
  public SearcherManager(Directory dir, SearcherWarmer warmer) throws IOException {
    this(dir, warmer, null);
  }

  /** Opens an initial searcher from the Directory.
   *
   * @param dir Directory to open the searcher from
   *
   * @param warmer optional {@link SearcherWarmer}.  Pass
   *        null if you don't require the searcher to warmed
   *        before going live.
   *
   * @param es optional ExecutorService so different segments can
   *        be searched concurrently (see {@link
   *        IndexSearcher#IndexSearcher(IndexReader,ExecutorService)}.  Pass null
   *        to search segments sequentially.
   *
   *  <p><b>NOTE</b>: the provided {@link SearcherWarmer} is
   *  not invoked for the initial searcher; you should
   *  warm it yourself if necessary.
   */
  public SearcherManager(Directory dir, SearcherWarmer warmer, ExecutorService es) throws IOException {
    this.es = es;
    currentSearcher = new IndexSearcher(IndexReader.open(dir), this.es);
    this.warmer = warmer;
  }

  @Override
  public boolean maybeReopen()
    throws  IOException {

    if (currentSearcher == null) {
      throw new AlreadyClosedException("this SearcherManager is closed");
    }

    // Ensure only 1 thread does reopen at once; other
    // threads just return immediately:
    if (reopening.tryAcquire()) {
      try {
        IndexReader newReader = IndexReader.openIfChanged(currentSearcher.getIndexReader());
        if (newReader != null) {
          IndexSearcher newSearcher = new IndexSearcher(newReader, es);
          boolean success = false;
          try {
            if (warmer != null) {
              warmer.warm(newSearcher);
            }
            swapSearcher(newSearcher);
            success = true;
          } finally {
            if (!success) {
              release(newSearcher);
            }
          }
          return true;
        } else {
          return false;
        }
      } finally {
        reopening.release();
      }
    } else {
      return false;
    }
  }

  @Override
  public void release(IndexSearcher searcher)
    throws IOException {
    searcher.getIndexReader().decRef();
  }

  // Replaces old searcher with new one - needs to be synced to make close() work
  private synchronized void swapSearcher(IndexSearcher newSearcher)
    throws IOException {
    IndexSearcher oldSearcher = currentSearcher;
    if (oldSearcher == null) {
      throw new AlreadyClosedException("this SearcherManager is closed");
    }
    currentSearcher = newSearcher;
    release(oldSearcher);
  }


  @Override
  public synchronized void close() throws IOException {
    if (currentSearcher != null) {
      // make sure we can call this more than once
      // closeable javadoc says:
      //   if this is already closed then invoking this method has no effect.
      swapSearcher(null);
    }
  }
}
