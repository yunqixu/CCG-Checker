/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package cn.jintongsoft;

import edu.uw.cs.lil.tiny.base.LispReader;
import edu.uw.cs.lil.tiny.base.concurrency.ITinyExecutor;
import edu.uw.cs.lil.tiny.base.concurrency.TinyExecutorService;
import edu.uw.cs.lil.tiny.base.hashvector.HashVectorFactory;
import edu.uw.cs.lil.tiny.base.hashvector.HashVectorFactory.HVFType;
import edu.uw.cs.lil.tiny.ccg.categories.syntax.Syntax;
import edu.uw.cs.lil.tiny.ccg.lexicon.ILexicon;
import edu.uw.cs.lil.tiny.ccg.lexicon.LexicalEntry;
import edu.uw.cs.lil.tiny.ccg.lexicon.Lexicon;
import edu.uw.cs.lil.tiny.ccg.lexicon.factored.lambda.FactoredLexicon;
import edu.uw.cs.lil.tiny.ccg.lexicon.factored.lambda.FactoredLexicon.FactoredLexicalEntry;
import edu.uw.cs.lil.tiny.data.sentence.Sentence;
import edu.uw.cs.lil.tiny.data.sentence.SentenceLengthFilter;
import edu.uw.cs.lil.tiny.data.singlesentence.SingleSentence;
import edu.uw.cs.lil.tiny.data.singlesentence.SingleSentenceDataset;
import edu.uw.cs.lil.tiny.data.utils.LabeledValidator;
import edu.uw.cs.lil.tiny.genlex.ccg.template.TemplateSupervisedGenlex;
import edu.uw.cs.lil.tiny.learn.ILearner;
import edu.uw.cs.lil.tiny.learn.validation.stocgrad.ValidationStocGrad;
import edu.uw.cs.lil.tiny.mr.lambda.FlexibleTypeComparator;
import edu.uw.cs.lil.tiny.mr.lambda.LogicLanguageServices;
import edu.uw.cs.lil.tiny.mr.lambda.LogicalConstant;
import edu.uw.cs.lil.tiny.mr.lambda.LogicalExpression;
import edu.uw.cs.lil.tiny.mr.lambda.Ontology;
import edu.uw.cs.lil.tiny.mr.lambda.ccg.LogicalExpressionCategoryServices;
import edu.uw.cs.lil.tiny.mr.lambda.ccg.SimpleFullParseFilter;
import edu.uw.cs.lil.tiny.mr.language.type.Type;
import edu.uw.cs.lil.tiny.mr.language.type.TypeRepository;
import edu.uw.cs.lil.tiny.parser.ccg.cky.CKYBinaryParsingRule;
import edu.uw.cs.lil.tiny.parser.ccg.cky.CKYUnaryParsingRule;
import edu.uw.cs.lil.tiny.parser.ccg.cky.multi.MultiCKYParser;
import edu.uw.cs.lil.tiny.parser.ccg.factoredlex.features.LexemeFeatureSet;
import edu.uw.cs.lil.tiny.parser.ccg.factoredlex.features.LexicalTemplateFeatureSet;
import edu.uw.cs.lil.tiny.parser.ccg.features.basic.LexicalFeatureSet;
import edu.uw.cs.lil.tiny.parser.ccg.features.basic.LexicalFeaturesInit;
import edu.uw.cs.lil.tiny.parser.ccg.features.basic.scorer.ExpLengthLexicalEntryScorer;
import edu.uw.cs.lil.tiny.parser.ccg.features.basic.scorer.SkippingSensitiveLexicalEntryScorer;
import edu.uw.cs.lil.tiny.parser.ccg.features.basic.scorer.UniformScorer;
import edu.uw.cs.lil.tiny.parser.ccg.features.lambda.LogicalExpressionCoordinationFeatureSet;
import edu.uw.cs.lil.tiny.parser.ccg.model.LexiconModelInit;
import edu.uw.cs.lil.tiny.parser.ccg.model.Model;
import edu.uw.cs.lil.tiny.parser.ccg.rules.lambda.PluralExistentialTypeShifting;
import edu.uw.cs.lil.tiny.parser.ccg.rules.lambda.ThatlessRelative;
import edu.uw.cs.lil.tiny.parser.ccg.rules.lambda.typeraising.ForwardTypeRaisedComposition;
import edu.uw.cs.lil.tiny.parser.ccg.rules.lambda.typeshifting.PrepositionTypeShifting;
import edu.uw.cs.lil.tiny.parser.ccg.rules.primitivebinary.application.BackwardApplication;
import edu.uw.cs.lil.tiny.parser.ccg.rules.primitivebinary.application.ForwardApplication;
import edu.uw.cs.lil.tiny.parser.ccg.rules.primitivebinary.composition.BackwardComposition;
import edu.uw.cs.lil.tiny.parser.ccg.rules.primitivebinary.composition.ForwardComposition;
import edu.uw.cs.lil.tiny.parser.ccg.rules.skipping.BackwardSkippingRule;
import edu.uw.cs.lil.tiny.parser.ccg.rules.skipping.ForwardSkippingRule;
import edu.uw.cs.lil.tiny.parser.graph.IGraphParser;
import edu.uw.cs.lil.tiny.test.Tester;
import edu.uw.cs.lil.tiny.test.stats.ExactMatchTestingStatistics;
import edu.uw.cs.utils.collections.ISerializableScorer;
import edu.uw.cs.utils.collections.SetUtils;
import edu.uw.cs.utils.log.thread.LoggingThreadFactory;
import java.io.File;
import java.io.IOException;
import java.io.StringReader;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import javax.swing.JOptionPane;

/**
 *
 * @author Administrator
 */
public class ccgParser {

    private LogicalExpressionCategoryServices categoryServices = null;
    private TypeRepository typeRepository = null;
    private IGraphParser<Sentence, LogicalExpression> parser = null;
    private TinyExecutorService executor = null;
    private Model<Sentence, LogicalExpression> model = null;
    private LabeledValidator<SingleSentence, LogicalExpression> validator = null;

    public ccgParser() {
        init();
    }

    private void init() {

        HashVectorFactory.DEFAULT = HVFType.TREE;
        
        final File typesFile = new File("types");
        final File ontologyFile = new File("ontology");
        
        typeRepository = new TypeRepository(typesFile);
        
        try {
            // Init the logical expression type system
            LogicLanguageServices.setInstance(
                    new LogicLanguageServices.Builder(typeRepository, new FlexibleTypeComparator())
                    .addConstantsToOntology(ontologyFile).setNumeralTypeName("i").closeOntology(false).build());
        } catch (final IOException e) {
            JOptionPane.showMessageDialog(null, "程序出错，自动关闭……");
            System.exit(0);
        }
        
        categoryServices = new LogicalExpressionCategoryServices(true, true);

        //Read NP list
//        File npLexiconFile = new File(resourceDir, "test_np-list.lex");
//        
//        npLexicon.addEntriesFromFile(npLexiconFile, categoryServices, Origin.FIXED_DOMAIN);

        executor = new TinyExecutorService(Runtime.getRuntime().availableProcessors(),
                new LoggingThreadFactory(), ITinyExecutor.DEFAULT_MONITOR_SLEEP);

        // //////////////////////////////////////////////////
        // CKY parser
        // //////////////////////////////////////////////////
        parser = new MultiCKYParser.Builder<>(
                categoryServices, executor, new SimpleFullParseFilter(SetUtils.createSingleton((Syntax) Syntax.S)))
                .setPruneLexicalCells(true).setPreChartPruning(true).setMaxNumberOfCellsInSpan(50)
                .addParseRule(new CKYBinaryParsingRule<>(
                        new ForwardComposition<>(categoryServices, 0)))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new BackwardComposition<>(categoryServices, 0)))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new ForwardApplication<>(categoryServices)))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new BackwardApplication<>(categoryServices)))
                .addParseRule(new CKYUnaryParsingRule<>(
                        new PrepositionTypeShifting()))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new ForwardSkippingRule<>(categoryServices)))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new BackwardSkippingRule<>(categoryServices)))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new ForwardTypeRaisedComposition(categoryServices)))
                .addParseRule(
                        new CKYBinaryParsingRule<>(new ThatlessRelative(categoryServices)))
                .addParseRule(new CKYBinaryParsingRule<>(
                        new PluralExistentialTypeShifting(categoryServices)))
                .build();

        // //////////////////////////////////////////////////
        // Model
        // //////////////////////////////////////////////////
        ISerializableScorer<LexicalEntry<LogicalExpression>> uniform0Scorer = new UniformScorer<LexicalEntry<LogicalExpression>>(
                0.0);
        SkippingSensitiveLexicalEntryScorer<LogicalExpression> skippingScorer = new SkippingSensitiveLexicalEntryScorer<LogicalExpression>(
                categoryServices.getEmptyCategory(), -1.0, uniform0Scorer);
        model = new Model.Builder<Sentence, LogicalExpression>()
                .setLexicon(new FactoredLexicon())
                .addLexicalFeatureSet(new LexicalFeatureSet.Builder<Sentence, LogicalExpression>()
                        .setInitialScorer(skippingScorer).build())
                .addLexicalFeatureSet(new LexemeFeatureSet.Builder<Sentence>().build())
                .addLexicalFeatureSet(new LexicalTemplateFeatureSet.Builder<Sentence>().setScale(0.1).build())
                .addParseFeatureSet(new LogicalExpressionCoordinationFeatureSet<Sentence>(true, true, true)).build();

        // //////////////////////////////////////////////////
        // Validation function
        // //////////////////////////////////////////////////
        validator = new LabeledValidator<SingleSentence, LogicalExpression>();
    }

    public boolean check(String rawSentence, String sentAnnotation, String lexAnnotation, String npAnnotation) {
        
        //Read Lexicon
        Set<LexicalEntry<LogicalExpression>> lexEntries = new HashSet<LexicalEntry<LogicalExpression>>();
        String[] lexs = lexAnnotation.split("\n");
        for (String lex : lexs){
            LexicalEntry<LogicalExpression> le = LexicalEntry.parse(lex,categoryServices,"seed");
            lexEntries.add(le);
        }
        
        //Read NP List
        ILexicon<LogicalExpression> npLexicon = new FactoredLexicon();
        String[] nps = npAnnotation.split("\n");
        for (String np : nps){
            LexicalEntry<LogicalExpression> le = LexicalEntry.parse(np, categoryServices, "seed");
            npLexicon.add(le);
        }
        
        //Read Semantics
        LogicalExpression semantics = LogicalExpression.read(sentAnnotation);
        
        //Factor Lexicon
        Lexicon<LogicalExpression> readLexicon = new Lexicon<LogicalExpression>(lexEntries);
        Lexicon<LogicalExpression> semiFactored = new Lexicon<LogicalExpression>();
        for (final LexicalEntry<LogicalExpression> entry : readLexicon.toCollection()) {
            for (final FactoredLexicalEntry factoredEntry : FactoredLexicon.factor(entry, true, true, 2)) {
                semiFactored.add(FactoredLexicon.factor(factoredEntry));
            }
        }
        
        TemplateSupervisedGenlex<SingleSentence> genlex = new TemplateSupervisedGenlex.Builder<SingleSentence>(4)
                .addTemplatesFromLexicon(semiFactored).build();
        
        
        //Build training set and testing set
        Sentence sent = new Sentence(rawSentence);
        SingleSentence ss = new SingleSentence(sent, semantics);
        ArrayList<SingleSentence> al = new ArrayList<SingleSentence>();
        al.add(ss);
        SingleSentenceDataset train = new SingleSentenceDataset(al);
        SingleSentenceDataset test = new SingleSentenceDataset(al);
        
        
        //Build tester and learner
        Tester<Sentence, LogicalExpression> tester = new Tester.Builder<Sentence, LogicalExpression>(test, parser).build();

        ILearner<Sentence, SingleSentence, Model<Sentence, LogicalExpression>> learner = new ValidationStocGrad.Builder<Sentence, SingleSentence, LogicalExpression>(
                train, parser, validator).setGenlex(genlex, categoryServices).setLexiconGenerationBeamSize(100)
                .setNumIterations(20).setProcessingFilter(new SentenceLengthFilter<SingleSentence>(50))
                .setTester(tester).setErrorDriven(true).setConflateGenlexAndPrunedParses(false).build();

        // //////////////////////////////////////////////////
        // Init model
        // //////////////////////////////////////////////////
        new LexiconModelInit<Sentence, LogicalExpression>(semiFactored).init(model);
        new LexicalFeaturesInit<Sentence, LogicalExpression>(semiFactored, "LEX",
                new ExpLengthLexicalEntryScorer<LogicalExpression>(10.0, 1.1)).init(model);
        new LexicalFeaturesInit<Sentence, LogicalExpression>(semiFactored, "XEME", 10.0).init(model);
        new LexiconModelInit<Sentence, LogicalExpression>(npLexicon).init(model);
        new LexicalFeaturesInit<Sentence, LogicalExpression>(npLexicon, "LEX", new ExpLengthLexicalEntryScorer<LogicalExpression>(10.0, 1.1)).init(model);
        new LexicalFeaturesInit<Sentence, LogicalExpression>(npLexicon, "XEME", 10.0).init(model);

        // //////////////////////////////////////////////////
        // Training
        // //////////////////////////////////////////////////
        learner.train(model);

        // //////////////////////////////////////////////////
        // Testing
        // //////////////////////////////////////////////////
        ExactMatchTestingStatistics<Sentence, LogicalExpression> stats = new ExactMatchTestingStatistics<Sentence, LogicalExpression>();
        tester.test(model, stats);
        
        if (stats.getF1() == 1.0){
            return true;
        }
        
        return false;
    }

    public LogicalExpression checkSentence(String s) {

        try {
            LogicalExpression le = LogicalExpression.read(s);
            return le;
        } catch (Exception e) {
            return null;
        }
    }

    public boolean checkLexicon(String s) {
        System.out.println(typeRepository.toString());
        String[] entries = s.split("\n");
        for (String entry : entries) {
            try {
                LexicalEntry<LogicalExpression> le = LexicalEntry.parse(entry, categoryServices, "seed");
            } catch (Exception e) {
                return false;
            }
        }
        return true;
    }
    
    public boolean checkNP(String newNP){
        System.out.println(typeRepository.toString());
        String[] nps = newNP.split("\n");
        for (String np : nps){
            try{
                LexicalEntry<LogicalExpression> le = LexicalEntry.parse(np, categoryServices, null);
            }
            catch (Exception e){
                return false;
            }
        }
        return true;
    }
    
    public boolean checkType(String types){
        String typeString = types.replaceAll("\\n", " ");
        try{
            final LispReader lispReader = new LispReader(new StringReader(typeString));
            while (lispReader.hasNext()) {
		Type type = typeRepository.createTypeFromString(lispReader.next());
                type = typeRepository.addType(type);
            }
        }
        catch (Exception e){
            e.printStackTrace();
            return false;
        }
        return true;
    }
    
    public void extractOntology(TreeSet<String> newOntologyEntries, TreeSet<String> existOntologyEntries, String semantics, Ontology ontology){
        Ontology staticOntology = new Ontology(ontology.getAllConstants(), true);
        String[] tokens = semantics.split("\\s+");
        
        for (String token : tokens){
            
            token = token.replaceAll("\\(", "");
            token = token.replaceAll("\\)", "");
           
            if (token.indexOf(":") == -1) continue;
            if (token.indexOf("$") != -1) continue;
            LogicalConstant lc = LogicalConstant.read(token);

            if (staticOntology.contains(lc)){
                existOntologyEntries.add(token);
            }
            else {
                newOntologyEntries.add(token);
            }
        }
    }
    
    public Ontology getOntology(){
        return LogicLanguageServices.getOntology();
    }
}
