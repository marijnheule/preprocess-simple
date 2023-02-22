#include <stdio.h>
#include <stdlib.h>

#define LRAT

FILE* lrat = NULL;

int *mask, *vIndex, *cIndex, stamp = 0, max;

int isSatisfied (int *clause) {
  if (clause[1] == 0) return 0;
  while (*clause) {
    if (mask[*clause] == stamp) return 1;
    clause++; }
  return 0; }

int removeFalsified (int *clause, int index) {
  int count = 0;
  int *_clause = clause;
  int flag = 0;

  if (lrat != NULL) {
    while (*clause) {
      if (mask[-*clause] == stamp)
        flag = 1;
      clause++; }
    clause = _clause;

    if (flag) {
      fprintf (lrat, "%i ", ++max);
      while (*clause) {
        if (mask[-*clause] != stamp)
          fprintf (lrat, "%i ", *clause);
        clause++; }
      fprintf (lrat, "0 ");
      clause = _clause;
      while (*clause) {
        if (mask[-*clause] == stamp)
          fprintf (lrat, "%i ", vIndex[abs(*clause)]);
        clause++; }
      fprintf (lrat, "%i 0\n", cIndex[index]);
      clause = _clause;

      fprintf (lrat, "%i d %i 0\n", max, cIndex[index]);
      cIndex[index] = max;
    }
  }

  while (*clause) {
    if (mask[-*clause] == stamp) {
//      printf ("c remove literal %i (%i) from clause %i\n", *clause, vIndex[abs(*clause)], index);
      count++;
    }
    else {
      *_clause++ = *clause; }
    clause++; }
  *_clause = 0;
  return count; }

int isTautology (int *clause) {
#ifndef LRAT
  stamp++;
  while (*clause) {
    if (mask[-*clause] == stamp) return 1;
    mask[*clause] = stamp;
    clause++; }
#endif
  return 0; }

int removeDuplicateLiterals (int *clause) {
  stamp++;
  int count = 0;
  int *_clause = clause;
  while (*clause) {
    if (mask[*clause] == stamp) count++;
    else {
      *_clause++ = *clause;
      mask[*clause] = stamp; }
    clause++; }
  *_clause = 0;
  return count; }

void printClause (int *clause) {
  while (*clause)
    printf("%i ", *clause++);
  printf("0\n"); }

int main (int argc, char** argv) {
  FILE *cnf=NULL, *map=NULL;

  cnf = fopen (argv[1], "r");

  if (argc > 2) {
    lrat = fopen (argv[2], "w"); }

  if (argc > 3) {
    map = fopen (argv[3], "w"); }

  int tmp, lit, nVar, nCls;
  tmp = fscanf (cnf, " p cnf %i %i ", &nVar, &nCls);
  mask = (int*) malloc (sizeof (int) * (2*nVar + 1));
  mask += nVar;

  max = nCls;

  int size = 0, *table, *cls;
  int tableSize = 2*nCls;
  table = (int*) malloc (sizeof(int) * tableSize);
  cls   = (int*) malloc (sizeof(int) * (nCls+1));
  nCls = 0;

  cls[0] = 0;
  while (1) {
    tmp = fscanf (cnf, " %i ", &lit);
    if (tmp != 1) break;
    if (size == tableSize) {
//      printf ("c resize table\n");
      tableSize *= 2;
      table = (int*) realloc (table, sizeof(int) * tableSize);
    }
    table [size++] = lit;
    if (lit == 0) cls[++nCls] = size; }

  int j = 0, k;
  for (int i = 0; i < nCls; i++) {
//    if (isTautology (table + cls[i])) {
//      printf ("c tautology %i\n", i);
//      continue;
//    }
    removeDuplicateLiterals (table + cls[i]);
    cls[j++] = cls[i]; }
  nCls = j;


  vIndex = (int*) malloc (sizeof(int) * (nVar+1));
  cIndex = (int*) malloc (sizeof(int) * nCls);

  int nSatis = 0;
  int *satis  = (int*) malloc (sizeof(int) * nCls);

  for (int i = 1; i <= nVar; i++) vIndex[i] = 0;
  for (int i = 0; i <  nCls; i++) cIndex[i] = i+1;

  stamp++;
  int iter = 1;
  while (iter) {
    iter = 0, j = 0;
    for (int i = 0; i < nCls; i++) {
      if (isSatisfied (table + cls[i])) {
        satis[nSatis++] = cIndex[i];
        iter = 1;
        continue; }
      if (table[cls[i] + 1] == 0) {
        if (mask[ table[cls[i]] ] != stamp) {
//          printf ("c found new unit %i\n", table[cls[i]]);
          vIndex[abs(table[cls[i]])] = cIndex[i];
          iter = 1; }
        mask[ table[cls[i]] ] = stamp; }
      if (removeFalsified (table + cls[i], i)) iter = 1;
      cIndex[j] = cIndex[i];
      cls[j++] = cls[i]; }
    nCls = j; }

/*
  // active, length, occ, list

  int* active = (int*) malloc (sizeof(int) * nCls);
  int* length = (int*) malloc (sizeof(int) * nCls);
  int* occ    = (int*) malloc (sizeof(int) * (nVar * 2 + 1)); occ += nVar;

  int l, lmax = 1;
  for (int i = 0; i < nCls; i++) {
    active[i] = 1;
    length[i] = 0;
    int* clause = table + cls[i];
    while (*clause) {
      length[i]++;
      occ[*clause++]++; }
    if (length[i] > lmax) lmax = length[i]; }

  int** list = (int**) malloc (sizeof(int*) * (nVar * 2 + 1)); list += nVar;
  for (int i = 1; i <= nVar; i++) {
    list[ i] = (int*) malloc (sizeof(int) * occ[ i]); occ[ i] = 0;
    list[-i] = (int*) malloc (sizeof(int) * occ[-i]); occ[-i] = 0; }

  for (int i = 0; i < nCls; i++) {
    int* clause = table + cls[i];
    while (*clause) {
      int lit = *clause++;
      list[lit][occ[lit]++] = i; } }

  // find subsumed clauses and make them inactive
  for (l = 2; l <= lmax; l++)
    for (int i = 0; i < nCls; i++)
      if (length[i] == l && active[i]) {
        stamp++;
        int* clause = table + cls[i];
        int rep = *clause;
        while (*clause) {
          lit = *clause++;
          mask[lit] = stamp;
          if (occ[rep] > occ[lit]) rep = lit; }
        for (j = 0; j < occ[rep]; j++) {
          int s = list[rep][j];
          if (s == i) continue;
          if (length[s] >= l && active[s]) {
            int matched = 0;
            int *super = table + cls[s];
            while (*super) {
              if (mask[*super++] == stamp) matched++; }
            if (matched == l) active[s] = 0; } } }

  // remove subsumed (inactive) clauses
  j = 0;
  for (int i = 0; i < nCls; i++) if (active[i]) cls[j++] = cls[i];
  nCls = j;
*/

  int nTaut = 0;
  for (int i = 0; i < nCls; i++)
    if (isTautology (table + cls[i]))
      nTaut++;

  if (lrat && nSatis) {
    fprintf (lrat, "%i d ", ++max);
    for (int i = 0; i < nCls; i++)
      if (isTautology (table + cls[i]))
        fprintf (lrat, "%i ", cIndex[i]);
    for (int i = 0; i < nSatis; i++)
      fprintf (lrat, "%i ", satis[i]);
    fprintf (lrat, "0\n");
  }

  int unsat = 0;

  printf("p cnf %i %i\n", nVar, nCls - nTaut);
  for (int i = 0; i < nCls; i++) {
    if (!isTautology (table + cls[i]))
      if (table[cls[i]] == 0) {
//        printf ("c found empty clause\n");
        unsat = 1; }
      printClause (table + cls[i]); }

  if (map != NULL) {
    for (int i = 0; i < nCls; i++)
      if (!isTautology (table + cls[i]))
        if (cIndex[i] != i+1)
          fprintf (map, "%i %i\n", i+1, cIndex[i]); }

  if (unsat) return 20;
  return 0;
}
