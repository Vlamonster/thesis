#!/bin/bash

output_file="proposal.md"

echo "# Master Thesis Proposal (Draft)" > $output_file
echo "" >> $output_file

echo "## Table of Contents" >> $output_file
echo "- [Background](#Background)" >> $output_file
echo "- [Research Question](#Research-question)" >> $output_file
echo "- [Motivation](#Motivation)" >> $output_file
echo "- [Approach](#Approach)" >> $output_file
echo "- [Expected Outcome](#Expected-outcome)" >> $output_file
echo "- [Related Work](#Related-work)" >> $output_file
echo "" >> $output_file

for section in background research_question motivation approach expected_outcome related_work; do
  section_with_spaces=$(echo $section | sed 's/_/ /g')
  echo "## ${section_with_spaces^}" >> $output_file
  cat ${section}.md >> $output_file
  echo "" >> $output_file
done

echo "Proposal built successfully into $output_file"
