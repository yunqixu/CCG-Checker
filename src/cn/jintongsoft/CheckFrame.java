/*
 * To change this license header, choose License Headers in Project Properties.
 * To change this template file, choose Tools | Templates
 * and open the template in the editor.
 */
package cn.jintongsoft;

import edu.uw.cs.lil.tiny.data.sentence.Sentence;
import edu.uw.cs.lil.tiny.mr.lambda.LogicalConstant;
import edu.uw.cs.lil.tiny.mr.lambda.LogicalExpression;
import edu.uw.cs.lil.tiny.mr.lambda.Ontology;
import edu.uw.cs.lil.tiny.mr.language.type.TypeRepository;
import edu.uw.cs.lil.tiny.test.stats.ExactMatchTestingStatistics;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.TreeSet;
import javax.swing.JOptionPane;

/**
 *
 * @author yunqixu
 * @date 20150202
 */
public class CheckFrame extends javax.swing.JFrame {
    
    private boolean isNPChecked;
    private boolean isLexiconChecked;
    private boolean isSentenceChecked;
    private boolean isChecked;
    
    private Ontology ontology;
    private TypeRepository typeRepository;
    
//    
//    private ccgParser cp = new ccgParser();
    
    
    private ExactMatchTestingStatistics<Sentence, LogicalExpression> stats = new ExactMatchTestingStatistics<Sentence, LogicalExpression>();
    
    /**
     * Creates new form CheckFrame
     */
    public CheckFrame() {
        super();
        this.setTitle("CCG标注助手");
        
        isLexiconChecked = false;
        isSentenceChecked = false;
        isChecked = false;
        initComponents();
    }

    /**
     * This method is called from within the constructor to initialize the form.
     * WARNING: Do NOT modify this code. The content of this method is always
     * regenerated by the Form Editor.
     */
    @SuppressWarnings("unchecked")
    // <editor-fold defaultstate="collapsed" desc="Generated Code">//GEN-BEGIN:initComponents
    private void initComponents() {

        jScrollPane1 = new javax.swing.JScrollPane();
        sentencePanel = new javax.swing.JPanel();
        sentenceLabel = new javax.swing.JLabel();
        rawSentence = new javax.swing.JTextField();
        sentenceAnnotationPanel = new javax.swing.JPanel();
        sentenceAnnotationLabel = new javax.swing.JLabel();
        sentenceAnnotationScrollPane = new javax.swing.JScrollPane();
        sentenceAnnotation = new javax.swing.JTextArea();
        checkSentenceButton = new javax.swing.JButton();
        lexiconAnnotationPanel = new javax.swing.JPanel();
        lexiconAnnotationLabel = new javax.swing.JLabel();
        lexiconAnnotationScrollPane = new javax.swing.JScrollPane();
        lexiconAnnotation = new javax.swing.JTextArea();
        checkLexiconButton = new javax.swing.JButton();
        npAnnotationLabel = new javax.swing.JLabel();
        jScrollPane4 = new javax.swing.JScrollPane();
        npAnnotation = new javax.swing.JTextArea();
        checkNPButton = new javax.swing.JButton();
        checkAllButton = new javax.swing.JButton();
        saveButton = new javax.swing.JButton();
        ontologyPanel = new javax.swing.JPanel();
        newOntologyLabel = new javax.swing.JLabel();
        jScrollPane2 = new javax.swing.JScrollPane();
        newOntologyEntriesTextArea = new javax.swing.JTextArea();
        existingOntologyLabel = new javax.swing.JLabel();
        jScrollPane3 = new javax.swing.JScrollPane();
        existingOntologyEntriesTextArea = new javax.swing.JTextArea();
        extractOntologyButton = new javax.swing.JButton();

        setDefaultCloseOperation(javax.swing.WindowConstants.EXIT_ON_CLOSE);

        sentencePanel.setBorder(javax.swing.BorderFactory.createTitledBorder(null, "sentence", javax.swing.border.TitledBorder.DEFAULT_JUSTIFICATION, javax.swing.border.TitledBorder.DEFAULT_POSITION, new java.awt.Font("华文中宋", 3, 12), new java.awt.Color(51, 51, 51))); // NOI18N

        sentenceLabel.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        sentenceLabel.setText("sentence:");

        javax.swing.GroupLayout sentencePanelLayout = new javax.swing.GroupLayout(sentencePanel);
        sentencePanel.setLayout(sentencePanelLayout);
        sentencePanelLayout.setHorizontalGroup(
            sentencePanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(sentencePanelLayout.createSequentialGroup()
                .addContainerGap()
                .addComponent(sentenceLabel)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(rawSentence, javax.swing.GroupLayout.PREFERRED_SIZE, 1018, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addContainerGap(23, Short.MAX_VALUE))
        );
        sentencePanelLayout.setVerticalGroup(
            sentencePanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(sentencePanelLayout.createSequentialGroup()
                .addContainerGap()
                .addGroup(sentencePanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                    .addComponent(sentenceLabel)
                    .addComponent(rawSentence, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addContainerGap(16, Short.MAX_VALUE))
        );

        sentenceAnnotationPanel.setBorder(javax.swing.BorderFactory.createTitledBorder(null, "sentence annotation", javax.swing.border.TitledBorder.DEFAULT_JUSTIFICATION, javax.swing.border.TitledBorder.DEFAULT_POSITION, new java.awt.Font("华文中宋", 3, 12), java.awt.Color.black)); // NOI18N

        sentenceAnnotationLabel.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        sentenceAnnotationLabel.setLabelFor(sentenceAnnotation);
        sentenceAnnotationLabel.setText("sentece annotation:");

        sentenceAnnotation.setColumns(20);
        sentenceAnnotation.setLineWrap(true);
        sentenceAnnotation.setRows(5);
        sentenceAnnotationScrollPane.setViewportView(sentenceAnnotation);

        checkSentenceButton.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        checkSentenceButton.setText("check sentence");
        checkSentenceButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                checkSentenceButtonActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout sentenceAnnotationPanelLayout = new javax.swing.GroupLayout(sentenceAnnotationPanel);
        sentenceAnnotationPanel.setLayout(sentenceAnnotationPanelLayout);
        sentenceAnnotationPanelLayout.setHorizontalGroup(
            sentenceAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(sentenceAnnotationPanelLayout.createSequentialGroup()
                .addContainerGap()
                .addGroup(sentenceAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                    .addComponent(checkSentenceButton)
                    .addGroup(sentenceAnnotationPanelLayout.createSequentialGroup()
                        .addComponent(sentenceAnnotationLabel)
                        .addGap(18, 18, 18)
                        .addComponent(sentenceAnnotationScrollPane, javax.swing.GroupLayout.PREFERRED_SIZE, 955, javax.swing.GroupLayout.PREFERRED_SIZE)))
                .addGap(0, 0, Short.MAX_VALUE))
        );
        sentenceAnnotationPanelLayout.setVerticalGroup(
            sentenceAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(sentenceAnnotationPanelLayout.createSequentialGroup()
                .addGroup(sentenceAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(sentenceAnnotationPanelLayout.createSequentialGroup()
                        .addContainerGap()
                        .addComponent(sentenceAnnotationLabel))
                    .addComponent(sentenceAnnotationScrollPane, javax.swing.GroupLayout.PREFERRED_SIZE, 54, javax.swing.GroupLayout.PREFERRED_SIZE))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                .addComponent(checkSentenceButton)
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );

        lexiconAnnotationPanel.setBorder(javax.swing.BorderFactory.createTitledBorder(null, "lexicon annotation", javax.swing.border.TitledBorder.DEFAULT_JUSTIFICATION, javax.swing.border.TitledBorder.DEFAULT_POSITION, new java.awt.Font("Arial Unicode MS", 3, 12), java.awt.Color.black)); // NOI18N

        lexiconAnnotationLabel.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        lexiconAnnotationLabel.setLabelFor(lexiconAnnotation);
        lexiconAnnotationLabel.setText("lexicon annotation:");

        lexiconAnnotation.setColumns(20);
        lexiconAnnotation.setRows(5);
        lexiconAnnotationScrollPane.setViewportView(lexiconAnnotation);

        checkLexiconButton.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        checkLexiconButton.setText("check lexicon");
        checkLexiconButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                checkLexiconButtonActionPerformed(evt);
            }
        });

        npAnnotationLabel.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        npAnnotationLabel.setText("np annotation:");

        npAnnotation.setColumns(20);
        npAnnotation.setRows(5);
        jScrollPane4.setViewportView(npAnnotation);

        checkNPButton.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        checkNPButton.setText("check NPs");
        checkNPButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                checkNPButtonActionPerformed(evt);
            }
        });

        checkAllButton.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        checkAllButton.setText("check ");
        checkAllButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                checkAllButtonActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout lexiconAnnotationPanelLayout = new javax.swing.GroupLayout(lexiconAnnotationPanel);
        lexiconAnnotationPanel.setLayout(lexiconAnnotationPanelLayout);
        lexiconAnnotationPanelLayout.setHorizontalGroup(
            lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                .addGroup(lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                    .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                        .addComponent(checkAllButton)
                        .addGap(387, 387, 387)
                        .addComponent(checkLexiconButton, javax.swing.GroupLayout.PREFERRED_SIZE, 116, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                        .addContainerGap()
                        .addComponent(lexiconAnnotationLabel)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.UNRELATED)
                        .addComponent(lexiconAnnotationScrollPane, javax.swing.GroupLayout.PREFERRED_SIZE, 439, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(8, 8, 8)))
                .addGap(88, 88, 88)
                .addGroup(lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                    .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                        .addComponent(npAnnotationLabel)
                        .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                        .addComponent(jScrollPane4, javax.swing.GroupLayout.PREFERRED_SIZE, 341, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addComponent(checkNPButton))
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
        lexiconAnnotationPanelLayout.setVerticalGroup(
            lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                .addContainerGap()
                .addGroup(lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(jScrollPane4, javax.swing.GroupLayout.DEFAULT_SIZE, 139, Short.MAX_VALUE)
                    .addComponent(lexiconAnnotationScrollPane)
                    .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                        .addGroup(lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                            .addComponent(npAnnotationLabel)
                            .addComponent(lexiconAnnotationLabel))
                        .addGap(0, 0, Short.MAX_VALUE)))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addGroup(lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(checkAllButton, javax.swing.GroupLayout.Alignment.TRAILING)
                    .addGroup(lexiconAnnotationPanelLayout.createSequentialGroup()
                        .addGroup(lexiconAnnotationPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.BASELINE)
                            .addComponent(checkLexiconButton)
                            .addComponent(checkNPButton))
                        .addGap(13, 13, 13))))
        );

        saveButton.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        saveButton.setText("save");
        saveButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                saveButtonActionPerformed(evt);
            }
        });

        ontologyPanel.setBorder(javax.swing.BorderFactory.createTitledBorder(null, "Ontology", javax.swing.border.TitledBorder.DEFAULT_JUSTIFICATION, javax.swing.border.TitledBorder.DEFAULT_POSITION, new java.awt.Font("Arial Unicode MS", 3, 12), java.awt.Color.black)); // NOI18N

        newOntologyLabel.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        newOntologyLabel.setText("new entries:");

        newOntologyEntriesTextArea.setColumns(20);
        newOntologyEntriesTextArea.setRows(5);
        jScrollPane2.setViewportView(newOntologyEntriesTextArea);

        existingOntologyLabel.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        existingOntologyLabel.setText("existing entries");

        existingOntologyEntriesTextArea.setColumns(20);
        existingOntologyEntriesTextArea.setRows(5);
        jScrollPane3.setViewportView(existingOntologyEntriesTextArea);

        extractOntologyButton.setFont(new java.awt.Font("Arial Unicode MS", 0, 12)); // NOI18N
        extractOntologyButton.setText("Extract Ontology");
        extractOntologyButton.addActionListener(new java.awt.event.ActionListener() {
            public void actionPerformed(java.awt.event.ActionEvent evt) {
                extractOntologyButtonActionPerformed(evt);
            }
        });

        javax.swing.GroupLayout ontologyPanelLayout = new javax.swing.GroupLayout(ontologyPanel);
        ontologyPanel.setLayout(ontologyPanelLayout);
        ontologyPanelLayout.setHorizontalGroup(
            ontologyPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(ontologyPanelLayout.createSequentialGroup()
                .addGroup(ontologyPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addComponent(extractOntologyButton)
                    .addGroup(ontologyPanelLayout.createSequentialGroup()
                        .addGap(29, 29, 29)
                        .addComponent(newOntologyLabel)
                        .addGap(18, 18, 18)
                        .addComponent(jScrollPane2, javax.swing.GroupLayout.PREFERRED_SIZE, 341, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addGap(106, 106, 106)
                        .addComponent(existingOntologyLabel)
                        .addGap(18, 18, 18)
                        .addComponent(jScrollPane3, javax.swing.GroupLayout.PREFERRED_SIZE, 447, javax.swing.GroupLayout.PREFERRED_SIZE)))
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
        ontologyPanelLayout.setVerticalGroup(
            ontologyPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(ontologyPanelLayout.createSequentialGroup()
                .addContainerGap()
                .addGroup(ontologyPanelLayout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(ontologyPanelLayout.createSequentialGroup()
                        .addComponent(existingOntologyLabel)
                        .addGap(0, 0, Short.MAX_VALUE))
                    .addGroup(ontologyPanelLayout.createSequentialGroup()
                        .addComponent(newOntologyLabel)
                        .addGap(0, 135, Short.MAX_VALUE))
                    .addComponent(jScrollPane2)
                    .addComponent(jScrollPane3))
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(extractOntologyButton)
                .addContainerGap())
        );

        javax.swing.GroupLayout layout = new javax.swing.GroupLayout(getContentPane());
        getContentPane().setLayout(layout);
        layout.setHorizontalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
                    .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING)
                        .addComponent(saveButton, javax.swing.GroupLayout.PREFERRED_SIZE, 103, javax.swing.GroupLayout.PREFERRED_SIZE)
                        .addComponent(ontologyPanel, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE))
                    .addGroup(layout.createParallelGroup(javax.swing.GroupLayout.Alignment.TRAILING, false)
                        .addComponent(sentencePanel, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(sentenceAnnotationPanel, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)
                        .addComponent(lexiconAnnotationPanel, javax.swing.GroupLayout.Alignment.LEADING, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE)))
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );
        layout.setVerticalGroup(
            layout.createParallelGroup(javax.swing.GroupLayout.Alignment.LEADING)
            .addGroup(layout.createSequentialGroup()
                .addContainerGap()
                .addComponent(sentencePanel, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(sentenceAnnotationPanel, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(lexiconAnnotationPanel, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(ontologyPanel, javax.swing.GroupLayout.PREFERRED_SIZE, javax.swing.GroupLayout.DEFAULT_SIZE, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addPreferredGap(javax.swing.LayoutStyle.ComponentPlacement.RELATED)
                .addComponent(saveButton, javax.swing.GroupLayout.PREFERRED_SIZE, 37, javax.swing.GroupLayout.PREFERRED_SIZE)
                .addContainerGap(javax.swing.GroupLayout.DEFAULT_SIZE, Short.MAX_VALUE))
        );

        pack();
    }// </editor-fold>//GEN-END:initComponents

    private void checkLexiconButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_checkLexiconButtonActionPerformed
        // TODO add your handling code here:
        String sentenceLexicon = lexiconAnnotation.getText();

        ccgParser cp = new ccgParser();
        boolean flag = cp.checkLexicon(sentenceLexicon);
        
        if (flag){
            JOptionPane.showMessageDialog(this, "标注正确");       
            isLexiconChecked = true;
        }
        else {
            JOptionPane.showMessageDialog(this, "标注错误，请检查");
        }
    }//GEN-LAST:event_checkLexiconButtonActionPerformed

    private void checkSentenceButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_checkSentenceButtonActionPerformed
        // TODO add your handling code here:
        String sentenceLambda = sentenceAnnotation.getText();
        
        ccgParser cp = new ccgParser();
        LogicalExpression l = cp.checkSentence(sentenceLambda);
        
        if (l != null){
            JOptionPane.showMessageDialog(this, "标注正确");
            isSentenceChecked = true;
        }
        else{
            JOptionPane.showMessageDialog(this, "标注错误，请检查");
        }
    }//GEN-LAST:event_checkSentenceButtonActionPerformed

    private void checkAllButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_checkAllButtonActionPerformed
        // TODO add your handling code here:
        if (! (isLexiconChecked && isSentenceChecked && isNPChecked)){
            JOptionPane.showMessageDialog(this, "请先检查整句标注和词汇标注的正确性");
            return;
        }
        
        String rSentence = rawSentence.getText();
        String sent = sentenceAnnotation.getText();
        String lex = lexiconAnnotation.getText();
        String np = npAnnotation.getText();
        
        ccgParser cp = new ccgParser();
        boolean flag = cp.check(rSentence,sent,lex,np);
        
        if (flag){
            JOptionPane.showMessageDialog(this, "标注正确");
            isChecked = true;
            isSentenceChecked = false;
            isLexiconChecked = false;
            isNPChecked = false;
        }
        else{
            JOptionPane.showMessageDialog(this, "标注不正确，请检查");
        }
    }//GEN-LAST:event_checkAllButtonActionPerformed

    private void saveButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_saveButtonActionPerformed
        // TODO add your handling code here:
        if (!isChecked){
            JOptionPane.showMessageDialog(this, "请先检查标注正确性");
            return;
        }
        
        String rawSent = rawSentence.getText();
        String sentAnnotation = sentenceAnnotation.getText();
        String lexAnnotation = lexiconAnnotation.getText();
        String ontologyAnnotation = newOntologyEntriesTextArea.getText();
        String npsAnnotation = npAnnotation.getText();

        sentAnnotation = (sentAnnotation.endsWith("\n") ? sentAnnotation : sentAnnotation + "\n");
        lexAnnotation = (lexAnnotation.endsWith("\n") ? lexAnnotation : lexAnnotation + "\n");
        ontologyAnnotation = (ontologyAnnotation.endsWith("\n") ? ontologyAnnotation : ontologyAnnotation + "\n");
        npsAnnotation = (npsAnnotation.endsWith("\n") ? npsAnnotation : npsAnnotation + "\n");
       
        File sentFile = new File("sent.ccg");
        if (!sentFile.exists()){
            try{
                sentFile.createNewFile();
            }
            catch (Exception e){
                JOptionPane.showMessageDialog(this, "保存出现错误");
                System.exit(0);
            }
        }
        
        File lexFile = new File("seed.lex");
        if (!lexFile.exists()){
            try{
                lexFile.createNewFile();
            }
            catch (Exception e){
                JOptionPane.showMessageDialog(this, "保存出现错误");
                System.exit(0);
            }
        }
        
        File ontologyFile = new File("ontology");
        if (!ontologyFile.exists()){
            try{
                ontologyFile.createNewFile();
            }
            catch (Exception e){
                JOptionPane.showMessageDialog(this, "保存出现错误");
                System.exit(0);
            }
        }
        
        File typeFile = new File("types");
        if (!typeFile.exists()){
            try{
                typeFile.createNewFile();
            }
            catch (Exception e){
                JOptionPane.showMessageDialog(this, "保存出现错误");
                System.exit(0);
            }
        }
        
        File npFile = new File("np-list");
        if (!npFile.exists()){
            try{
                npFile.createNewFile();
            }
            catch (Exception e){
                JOptionPane.showMessageDialog(this, "保存出现错误");
                System.exit(0);
            }
        }
        
        try{
            FileWriter fw = new FileWriter(sentFile, true);
            BufferedWriter bw = new BufferedWriter(fw);
            bw.append(rawSent+"\n");
            bw.append(sentAnnotation);
            bw.append("\n");
            bw.flush();
            bw.close();
            
            fw = new FileWriter(lexFile, true);
            bw = new BufferedWriter(fw);
            bw.append(lexAnnotation);
            bw.append("\n");
            bw.flush();
            bw.close();
            
            fw = new FileWriter(ontologyFile, true);
            bw = new BufferedWriter(fw);
            bw.append(ontologyAnnotation);
            bw.append("\n");
            bw.flush();
            bw.close();
            
            fw = new FileWriter(npFile, true);
            bw = new BufferedWriter(fw);
            bw.append(npsAnnotation);
            bw.append("\n");
            bw.flush();
            bw.close();
            
            JOptionPane.showMessageDialog(this, "保存成功");
            
            isChecked = false;
        }
        catch (Exception e){
            JOptionPane.showMessageDialog(this, "保存错误");
            System.exit(0);
        }
    }//GEN-LAST:event_saveButtonActionPerformed

    private void extractOntologyButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_extractOntologyButtonActionPerformed
        // TODO add your handling code here:
        TreeSet<String> newOntologyEntries = new TreeSet<String>();
        TreeSet<String> existOntologyEntries = new TreeSet<String>();
        
        String semantics = sentenceAnnotation.getText();
        
        ccgParser cp = new ccgParser();
        ontology = cp.getOntology();
        cp.extractOntology(newOntologyEntries, existOntologyEntries, semantics, ontology);
        
        String exist = "";
        for (String s : existOntologyEntries){
            exist = exist + s + "\n";
        }
        
        String newAdd = "";
        for (String s : newOntologyEntries){
            newAdd = newAdd + s + "\n";
        }
        
        existingOntologyEntriesTextArea.setText(exist);
        newOntologyEntriesTextArea.setText(newAdd);
    }//GEN-LAST:event_extractOntologyButtonActionPerformed
    
    private void checkNPButtonActionPerformed(java.awt.event.ActionEvent evt) {//GEN-FIRST:event_checkNPButtonActionPerformed
        // TODO add your handling code here:
        String newNP = npAnnotation.getText();
        
        ccgParser cp = new ccgParser();
        boolean flag = cp.checkNP(newNP);
        if (flag){
            JOptionPane.showMessageDialog(this, "标注正确");
            isNPChecked = true;
        }
        else {
            JOptionPane.showMessageDialog(this, "标注错误，请检查");
        }
    }//GEN-LAST:event_checkNPButtonActionPerformed

    /**
     * @param args the command line arguments
     */
    public static void main(String args[]) {
        /* Set the Nimbus look and feel */
        //<editor-fold defaultstate="collapsed" desc=" Look and feel setting code (optional) ">
        try {
            for (javax.swing.UIManager.LookAndFeelInfo info : javax.swing.UIManager.getInstalledLookAndFeels()) {
                if ("Nimbus".equals(info.getName())) {
                    javax.swing.UIManager.setLookAndFeel(info.getClassName());
                    break;
                }
            }
        } catch (ClassNotFoundException ex) {
            java.util.logging.Logger.getLogger(CheckFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (InstantiationException ex) {
            java.util.logging.Logger.getLogger(CheckFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (IllegalAccessException ex) {
            java.util.logging.Logger.getLogger(CheckFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        } catch (javax.swing.UnsupportedLookAndFeelException ex) {
            java.util.logging.Logger.getLogger(CheckFrame.class.getName()).log(java.util.logging.Level.SEVERE, null, ex);
        }
        //</editor-fold>

        /* Create and display the form */
        java.awt.EventQueue.invokeLater(new Runnable() {
            @Override
            public void run() {
                new CheckFrame().setVisible(true);
               
            }
        });
    }

    // Variables declaration - do not modify//GEN-BEGIN:variables
    private javax.swing.JButton checkAllButton;
    private javax.swing.JButton checkLexiconButton;
    private javax.swing.JButton checkNPButton;
    private javax.swing.JButton checkSentenceButton;
    private javax.swing.JTextArea existingOntologyEntriesTextArea;
    private javax.swing.JLabel existingOntologyLabel;
    private javax.swing.JButton extractOntologyButton;
    private javax.swing.JScrollPane jScrollPane1;
    private javax.swing.JScrollPane jScrollPane2;
    private javax.swing.JScrollPane jScrollPane3;
    private javax.swing.JScrollPane jScrollPane4;
    private javax.swing.JTextArea lexiconAnnotation;
    private javax.swing.JLabel lexiconAnnotationLabel;
    private javax.swing.JPanel lexiconAnnotationPanel;
    private javax.swing.JScrollPane lexiconAnnotationScrollPane;
    private javax.swing.JTextArea newOntologyEntriesTextArea;
    private javax.swing.JLabel newOntologyLabel;
    private javax.swing.JTextArea npAnnotation;
    private javax.swing.JLabel npAnnotationLabel;
    private javax.swing.JPanel ontologyPanel;
    private javax.swing.JTextField rawSentence;
    private javax.swing.JButton saveButton;
    private javax.swing.JTextArea sentenceAnnotation;
    private javax.swing.JLabel sentenceAnnotationLabel;
    private javax.swing.JPanel sentenceAnnotationPanel;
    private javax.swing.JScrollPane sentenceAnnotationScrollPane;
    private javax.swing.JLabel sentenceLabel;
    private javax.swing.JPanel sentencePanel;
    // End of variables declaration//GEN-END:variables
}
