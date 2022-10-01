#include <stdio.h>
#include <stdlib.h>

#define PUREGATE

int *mask, stamp = 0;

int isSatisfied (int *clause) {
  while (*clause) {
    if (mask[*clause] == stamp) return 1;
    clause++; }
  return 0; }

int removeFalsified (int *clause) {
  int count = 0;
  int *_clause = clause;
  while (*clause) {
    if (mask[-*clause] == stamp) count++;
    else {
      *_clause++ = *clause; }
    clause++; }
  *_clause = 0;
  return count; }

int isTautology (int *clause) {
  stamp++;
  while (*clause) {
    if (mask[-*clause] == stamp) return 1;
    mask[*clause] = stamp;
    clause++; }
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
  FILE* cnf;

  cnf = fopen (argv[1], "r");

  int tmp, lit, nVar, nCls;
  tmp = fscanf (cnf, " p cnf %i %i ", &nVar, &nCls);
  mask = (int*) malloc (sizeof (int) * (2*nVar + 1));
  mask += nVar;

  int size = 0, *table, *cls;
  table = (int*) malloc (sizeof(int) * 100 * nCls);
  cls   = (int*) malloc (sizeof(int) * (nCls+1));
  nCls = 0;

  cls[0] = 0;
  while (1) {
    tmp = fscanf (cnf, " %i ", &lit);
    if (tmp != 1) break;
    table [size++] = lit;
    if (lit == 0) cls[++nCls] = size; }

  int i, j = 0, k;
  for (i = 0; i < nCls; i++) {
    if (isTautology (table + cls[i])) continue;
    removeDuplicateLiterals (table + cls[i]);
    cls[j++] = cls[i]; }
  nCls = j;

  stamp++;
  int iter = 1;
  while (iter) {
    iter = 0, j = 0;
    for (i = 0; i < nCls; i++) {
      if (isSatisfied (table + cls[i])) { iter = 1; continue; }
      if (table[cls[i] + 1] == 0) {
        if (mask[ table[cls[i]] ] != stamp) iter = 1;
        mask[ table[cls[i]] ] = stamp; }
      if (removeFalsified (table + cls[i])) iter = 1;
      cls[j++] = cls[i]; }
    nCls = j; }

  int unitStamp = stamp;

  // active, length, occ, list

  int* active = (int*) malloc (sizeof(int) * nCls);
  int* length = (int*) malloc (sizeof(int) * nCls);
  int* occ    = (int*) malloc (sizeof(int) * (nVar * 2 + 1)); occ += nVar;

  int l, lmax = 1;
  for (i = 0; i < nCls; i++) {
    active[i] = 1; length[i] = 0;
    int* clause = table + cls[i];
    while (*clause) {
      length[i]++;
      occ[*clause++]++; }
    if (length[i] > lmax) lmax = length[i]; }


  int** list = (int**) malloc (sizeof(int*) * (nVar * 2 + 1)); list += nVar;
  for (i = 1; i <= nVar; i++) {
    list[ i] = (int*) malloc (sizeof(int) * occ[ i]); occ[ i] = 0;
    list[-i] = (int*) malloc (sizeof(int) * occ[-i]); occ[-i] = 0; }

  for (i = 0; i < nCls; i++) {
    int* clause = table + cls[i];
    while (*clause) {
      int lit = *clause++;
      list[lit][occ[lit]++] = i; } }

  // find subsumed clauses and make them inactive
  for (l = 2; l <= lmax; l++)
    for (i = 0; i < nCls; i++)
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

#ifdef PUREGATE
  // printf ("c pure gate\n");
  iter = 1;
  while (iter) {
    iter = 0;
  for (i = 1; i <= nVar; i++) {
    if ((occ[i] == 0) || (occ[-i] == 0)) continue;

    int pos = 0, neg = 0;
    for (j = 0; j < occ[i]; j++) {
      int c = list[i][j];
      if (active[c]) {
        stamp++;
        pos = 1;
        int* clause = table + cls[c];
        while (*clause) mask[*clause++] = stamp;
        for (k = 0; k < occ[-i]; k++) {
           int b = list[-i][k];
           if (active[b]) {
             int count = 0;
             int* blocked = table + cls[b];
             while (*blocked) if (mask[-(*blocked++)] >= stamp) count++;
             if (count  < 2) goto nextVar;
             if (count == 2) {
               blocked = table + cls[b];
               while (*blocked) if (mask[-(*blocked++)] == stamp) mask[-blocked[-1]] = stamp + 1; } } }
        stamp++;
        clause = table + cls[c];
        while (*clause) if (mask[*clause++] != stamp) goto nextVar; } }

    for (j = 0; j < occ[-i]; j++) {
      int c = list[-i][j];
      if (active[c]) {
        stamp++;
        neg = 1;
        int* clause = table + cls[c];
        while (*clause) mask[*clause++] = stamp;
        for (k = 0; k < occ[i]; k++) {
           int b = list[i][k];
           if (active[b]) {
             int count = 0;
             int* blocked = table + cls[b];
             while (*blocked) if (mask[-(*blocked++)] >= stamp) count++;
             if (count  < 2) goto nextVar;
             if (count == 2) {
               blocked = table + cls[b];
               while (*blocked) if (mask[-(*blocked++)] == stamp) mask[-blocked[-1]] = stamp + 1; } } }
        stamp++;
        clause = table + cls[c];
        while (*clause) if (mask[*clause++] != stamp) goto nextVar; } }

    if ((pos == 0) || (neg == 0)) goto nextVar;
    iter = 1;
    mask[ i] = unitStamp;
    for (j = 0; j < occ[ i]; j++) active[list[ i][j]] = 0;
    for (j = 0; j < occ[-i]; j++) active[list[-i][j]] = 0;
    printf("c found pure gate: %i\n", i);
    nextVar:;
  } }
#endif

  // remove subsumed (inactive) clauses
  j = 0;
  for (i = 0; i < nCls; i++) if (active[i]) cls[j++] = cls[i];
  nCls = j;

  int units = 0;
  for (i = 1; i <= nVar; i++)
    if (mask[i] == unitStamp || mask[-i] == unitStamp) units++;

  printf("p cnf %i %i\n", nVar, nCls + units);
  for (i = 0; i < nCls; i++) {
    printClause (table + cls[i]); }

  for (i = 1; i <= nVar; i++) {
    if (mask[ i] == unitStamp && mask[-i] == unitStamp) printf("0\n");
    if (mask[ i] == unitStamp)                          printf("%i 0\n",  i);
    if (mask[-i] == unitStamp)                          printf("%i 0\n", -i); }
}
