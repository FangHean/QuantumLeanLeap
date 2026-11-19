import unittest
import bench

class BenchTests(unittest.TestCase):
    def test_pass_at_k(self):
        self.assertEqual(bench.pass_at_k(5, 0, 2), 0)
        self.assertEqual(bench.pass_at_k(5, 5, 2), 1)
        self.assertAlmostEqual(bench.pass_at_k(5, 1, 2), .4)
        self.assertIsNone(bench.pass_at_k(1, 1, 2))
    def test_missing_task_not_dropped(self):
        row=dict(model='m',task_id='a',status='accepted',verification_seconds=0)
        s=bench.summarize([row],{'a':{},'b':{}},[1])['m']
        self.assertEqual(s['solved_fraction_full_suite'], .5)
        self.assertIsNone(s['pass_at_k']['1'])
    def test_model_separation(self):
        rows=[dict(model=m,task_id='a',status=s,verification_seconds=0)
              for m,s in [('good','accepted'),('bad','timeout')]]
        r=bench.summarize(rows,{'a':{}},[1])
        self.assertEqual(r['good']['pass_at_k']['1'],1)
        self.assertEqual(r['bad']['pass_at_k']['1'],0)
    def test_source_rejects_placeholders_and_commands(self):
        t=next(iter(bench.load_tasks().values()))
        for proof in ['by sorry','by admit','by native_decide','by run_tac pure ()',
                      'by trivial\naxiom fake : False', 'by trivial\n#print axioms x',None,'']:
            with self.subTest(proof=proof),self.assertRaises(ValueError): bench.source(t,proof)
    def test_axiom_whitelist(self):
        for text in ['', "'QLLBenchSubmission.accepted' depends on axioms: [sorryAx]",
                     "'QLLBenchSubmission.accepted' depends on axioms: [Evil.axiom]"]:
            with self.assertRaises(ValueError): bench.audit(text)
        self.assertEqual(bench.audit("'QLLBenchSubmission.accepted' depends on axioms: [propext]"),['propext'])
    def test_duplicate_axiom_report(self):
        text="'QLLBenchSubmission.accepted' does not depend on any axioms"
        with self.assertRaises(ValueError): bench.audit(text+text)
    def test_prompt_has_no_reference(self):
        t=next(iter(bench.load_tasks().values()))
        self.assertIn('<PROOF>',bench.prompt(t))
        self.assertNotIn('by rfl',bench.prompt(t))
    def test_suite_unique(self):
        self.assertEqual(len(bench.load_tasks()),12)
if __name__=='__main__': unittest.main()
