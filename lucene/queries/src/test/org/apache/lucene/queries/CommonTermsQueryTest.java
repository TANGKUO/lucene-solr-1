package org.apache.lucene.queries;

/*
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
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;

import org.apache.lucene.document.Document;
import org.apache.lucene.document.Field;
import org.apache.lucene.index.DirectoryReader;
import org.apache.lucene.index.IndexReader;
import org.apache.lucene.index.RandomIndexWriter;
import org.apache.lucene.index.SlowCompositeReaderWrapper;
import org.apache.lucene.index.Term;
import org.apache.lucene.index.Terms;
import org.apache.lucene.index.TermsEnum;
import org.apache.lucene.search.BooleanClause;
import org.apache.lucene.search.BooleanClause.Occur;
import org.apache.lucene.search.BooleanQuery;
import org.apache.lucene.search.IndexSearcher;
import org.apache.lucene.search.ScoreDoc;
import org.apache.lucene.search.TermQuery;
import org.apache.lucene.search.TopDocs;
import org.apache.lucene.store.Directory;
import org.apache.lucene.util.BytesRef;
import org.apache.lucene.util.LineFileDocs;
import org.apache.lucene.util.LuceneTestCase;
import org.apache.lucene.util.PriorityQueue;

public class CommonTermsQueryTest extends LuceneTestCase {
  
  public void testBasics() throws IOException {
    Directory dir = newDirectory();
    RandomIndexWriter w = new RandomIndexWriter(random(), dir);
    String[] docs = new String[] {"this is the end of the world right",
        "is this it or maybe not",
        "this is the end of the universe as we know it",
        "there is the famous restaurant at the end of the universe",};
    for (int i = 0; i < docs.length; i++) {
      Document doc = new Document();
      doc.add(newStringField("id", "" + i, Field.Store.YES));
      doc.add(newTextField("field", docs[i], Field.Store.NO));
      w.addDocument(doc);
    }
    
    IndexReader r = w.getReader();
    IndexSearcher s = newSearcher(r);
    {
      CommonTermsQuery query = new CommonTermsQuery(Occur.SHOULD, Occur.SHOULD,
          random().nextBoolean() ? 2.0f : 0.5f);
      query.add(new Term("field", "is"));
      query.add(new Term("field", "this"));
      query.add(new Term("field", "end"));
      query.add(new Term("field", "world"));
      query.add(new Term("field", "universe"));
      query.add(new Term("field", "right"));
      TopDocs search = s.search(query, 10);
      assertEquals(search.totalHits, 3);
      assertEquals("0", r.document(search.scoreDocs[0].doc).get("id"));
      assertEquals("2", r.document(search.scoreDocs[1].doc).get("id"));
      assertEquals("3", r.document(search.scoreDocs[2].doc).get("id"));
    }
    
    { // only high freq
      CommonTermsQuery query = new CommonTermsQuery(Occur.SHOULD, Occur.SHOULD,
          random().nextBoolean() ? 2.0f : 0.5f);
      query.add(new Term("field", "is"));
      query.add(new Term("field", "this"));
      query.add(new Term("field", "end"));
      TopDocs search = s.search(query, 10);
      assertEquals(search.totalHits, 2);
      assertEquals("0", r.document(search.scoreDocs[0].doc).get("id"));
      assertEquals("2", r.document(search.scoreDocs[1].doc).get("id"));
    }
    
    { // low freq is mandatory
      CommonTermsQuery query = new CommonTermsQuery(Occur.SHOULD, Occur.MUST,
          random().nextBoolean() ? 2.0f : 0.5f);
      query.add(new Term("field", "is"));
      query.add(new Term("field", "this"));
      query.add(new Term("field", "end"));
      query.add(new Term("field", "world"));
      
      TopDocs search = s.search(query, 10);
      assertEquals(search.totalHits, 1);
      assertEquals("0", r.document(search.scoreDocs[0].doc).get("id"));
    }
    
    { // low freq is mandatory
      CommonTermsQuery query = new CommonTermsQuery(Occur.SHOULD, Occur.MUST,
          random().nextBoolean() ? 2.0f : 0.5f);
      query.add(new Term("field", "restaurant"));
      query.add(new Term("field", "universe"));
      
      TopDocs search = s.search(query, 10);
      assertEquals(search.totalHits, 1);
      assertEquals("3", r.document(search.scoreDocs[0].doc).get("id"));
      
    }
    r.close();
    w.close();
    dir.close();
  }
  
  private static Occur randomOccur(Random random) {
    return random.nextBoolean() ? Occur.MUST : Occur.SHOULD;
  }
  
  public void testNullTerm() {
    Random random = random();
    CommonTermsQuery query = new CommonTermsQuery(randomOccur(random),
        randomOccur(random), random().nextFloat());
    try {
      query.add(null);
      fail("null values are not supported");
    } catch (IllegalArgumentException ex) {
      
    }
  }
  
  public void testRandomIndex() throws IOException {
    Directory dir = newDirectory();
    RandomIndexWriter w = new RandomIndexWriter(random(), dir);
    createRandomIndex(atLeast(100), w, random().nextLong());
    DirectoryReader reader = w.getReader();
    SlowCompositeReaderWrapper wrapper = new SlowCompositeReaderWrapper(reader);
    String field = "body";
    Terms terms = wrapper.terms(field);
    PriorityQueue<TermAndFreq> lowFreqQueue = new PriorityQueue<CommonTermsQueryTest.TermAndFreq>(
        5) {
      
      @Override
      protected boolean lessThan(TermAndFreq a, TermAndFreq b) {
        return a.freq > b.freq;
      }
      
    };
    PriorityQueue<TermAndFreq> highFreqQueue = new PriorityQueue<CommonTermsQueryTest.TermAndFreq>(
        5) {
      
      @Override
      protected boolean lessThan(TermAndFreq a, TermAndFreq b) {
        return a.freq < b.freq;
      }
      
    };
    try {
      TermsEnum iterator = terms.iterator(null);
      while (iterator.next() != null) {
        if (highFreqQueue.size() < 5) {
          highFreqQueue.add(new TermAndFreq(
              BytesRef.deepCopyOf(iterator.term()), iterator.docFreq()));
          lowFreqQueue.add(new TermAndFreq(
              BytesRef.deepCopyOf(iterator.term()), iterator.docFreq()));
        } else {
          if (highFreqQueue.top().freq < iterator.docFreq()) {
            highFreqQueue.top().freq = iterator.docFreq();
            highFreqQueue.top().term = BytesRef.deepCopyOf(iterator.term());
            highFreqQueue.updateTop();
          }
          
          if (lowFreqQueue.top().freq > iterator.docFreq()) {
            lowFreqQueue.top().freq = iterator.docFreq();
            lowFreqQueue.top().term = BytesRef.deepCopyOf(iterator.term());
            lowFreqQueue.updateTop();
          }
        }
      }
      int lowFreq = lowFreqQueue.top().freq;
      int highFreq = highFreqQueue.top().freq;
      assumeTrue("unlucky index", highFreq - 1 > lowFreq);
      List<TermAndFreq> highTerms = queueToList(highFreqQueue);
      List<TermAndFreq> lowTerms = queueToList(lowFreqQueue);
      
      IndexSearcher searcher = new IndexSearcher(reader);
      Occur lowFreqOccur = randomOccur(random());
      BooleanQuery verifyQuery = new BooleanQuery();
      CommonTermsQuery cq = new CommonTermsQuery(randomOccur(random()),
          lowFreqOccur, highFreq - 1, random().nextBoolean());
      for (TermAndFreq termAndFreq : lowTerms) {
        cq.add(new Term(field, termAndFreq.term));
        verifyQuery.add(new BooleanClause(new TermQuery(new Term(field,
            termAndFreq.term)), lowFreqOccur));
      }
      for (TermAndFreq termAndFreq : highTerms) {
        cq.add(new Term(field, termAndFreq.term));
      }
      
      TopDocs cqSearch = searcher.search(cq, reader.maxDoc());
      TopDocs verifySearch = searcher.search(verifyQuery, reader.maxDoc());
      
      assertEquals(verifySearch.totalHits, cqSearch.totalHits);
      Set<Integer> hits = new HashSet<Integer>();
      for (ScoreDoc doc : verifySearch.scoreDocs) {
        hits.add(doc.doc);
      }
      
      for (ScoreDoc doc : cqSearch.scoreDocs) {
        assertTrue(hits.remove(doc.doc));
      }
      
      assertTrue(hits.isEmpty());
    } finally {
      reader.close();
      w.close();
      dir.close();
    }
    
  }
  
  private static List<TermAndFreq> queueToList(PriorityQueue<TermAndFreq> queue) {
    List<TermAndFreq> terms = new ArrayList<CommonTermsQueryTest.TermAndFreq>();
    while (queue.size() > 0) {
      terms.add(queue.pop());
    }
    return terms;
  }
  
  private static class TermAndFreq {
    BytesRef term;
    int freq;
    
    public TermAndFreq(BytesRef term, int freq) {
      this.term = term;
      this.freq = freq;
      
    }
    
  }
  
  /**
   * populates a writer with random stuff. this must be fully reproducable with
   * the seed!
   */
  public static void createRandomIndex(int numdocs, RandomIndexWriter writer,
      long seed) throws IOException {
    Random random = new Random(seed);
    // primary source for our data is from linefiledocs, its realistic.
    LineFileDocs lineFileDocs = new LineFileDocs(random);
    
    // TODO: we should add other fields that use things like docs&freqs but omit
    // positions,
    // because linefiledocs doesn't cover all the possibilities.
    for (int i = 0; i < numdocs; i++) {
      writer.addDocument(lineFileDocs.nextDoc());
    }
    
    lineFileDocs.close();
  }
}
