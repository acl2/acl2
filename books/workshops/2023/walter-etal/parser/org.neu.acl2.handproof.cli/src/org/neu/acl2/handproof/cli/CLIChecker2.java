package org.neu.acl2.handproof.cli;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileWriter;
import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.io.OutputStreamWriter;
import java.io.PrintStream;
import java.nio.charset.StandardCharsets;
import java.nio.file.FileSystems;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.concurrent.Callable;

import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.ecore.resource.ResourceSet;
import org.eclipse.xtext.diagnostics.Severity;
import org.eclipse.xtext.generator.GeneratorDelegate;
import org.eclipse.xtext.generator.InMemoryFileSystemAccess;
import org.eclipse.xtext.util.CancelIndicator;
import org.eclipse.xtext.validation.CheckMode;
import org.eclipse.xtext.validation.IResourceValidator;
import org.eclipse.xtext.validation.Issue;
import org.json.JSONWriter;
import org.neu.acl2.handproof.HandProofStandaloneSetup;
import org.neu.acl2.handproof.validation.HandProofValidator;
import org.neu.acl2.handproof.validation.IValidationFilePathProvider;
import org.neu.acl2.handproof.validation.IValidationMessageHandler;
import org.neu.acl2.handproof.validation.LoggingValidationMessageHandler;

import com.google.inject.Injector;

import picocli.CommandLine;
import picocli.CommandLine.ArgGroup;
import picocli.CommandLine.Command;
import picocli.CommandLine.Option;
import picocli.CommandLine.Parameters;

@Command(description = "Run the proof checker on a file",
name = "checker", mixinStandardHelpOptions = true, version = "checker 0.0.1", exitCodeOnExecutionException = -1)
public class CLIChecker2 implements Callable<Integer> {
    private enum CheckerOutputFormat {
        plain,
        json
    }

    @Parameters(index = "0", description = "The proof file to check")
    private File file;

    @Option(names = "--no-full", negatable = true, description = "Whether or not to run a full check of the proof file. True by default.")
    boolean fullCheck = true;

    @Option(names = "--show-output", description = "Whether or not to display the full output from the backend.")
    boolean showOutput = false;

    @Option(names = "--show-timings", description = "Whether or not to display timing information from the backend.")
    boolean showTimings = false;

    @Option(names = { "--format" }, description = "The output format to use. Valid options are ${COMPLETION-CANDIDATES}" )
    CheckerOutputFormat outputFormat = CheckerOutputFormat.plain;

    @ArgGroup(exclusive = false)
    private GenerateOptions generateOptions;

    static class GenerateOptions {
        @Option(names = {"-g", "--generate"},
                description = "Convert the proof file into a file which can be used by the ACL2s backend directly",
                required = true)
        boolean generate;

        @Option(names = {"-o", "--out"} , description = "File to output")
        private File outfile;
    }

    public static void main(String... args) throws Exception {
        int exitCode = new CommandLine(new CLIChecker2()).execute(args);
        System.exit(exitCode);
    }

    private void outputPlain(OutputStream outStream, java.net.URI sourceFile, List<Issue> issues) throws IOException {
        PrintStream out = new PrintStream(outStream);
        // We need to read in the file so that we can print out the relevant parts of the file when printing out error messages.
        byte[] bytes = Files.readAllBytes(Paths.get(sourceFile));
        String text = new String(bytes, StandardCharsets.UTF_8);

        for (Issue issue: issues) {
            // This issue is used to provide the web client with some extra information.
            // If the user specifies that they want to see this information, print it out.
            if(issue.getCode().equals(HandProofValidator.VALIDATION_OUTPUT)) {
                if(showOutput) {
                    out.println("OUTPUT: " + issue.getData()[0]);
                }
                continue;
            } else if(issue.getCode().equals(HandProofValidator.VALIDATION_TIMING)) {
                if(showTimings) {
                    out.println("TIMING: " + issue.getMessage());
                }
            } else {
                switch (issue.getSeverity()) {
                case ERROR:
                    out.println("ERROR: " + issue.getMessage());
                    break;
                case WARNING:
                    out.println("WARNING: " + issue.getMessage());
                    break;
                case INFO:
                    out.println("INFO: " + issue.getMessage());
                    break;
                default:
                    continue;
                }
                out.println("Line " + issue.getLineNumber() + ", Col " + issue.getColumn());
                // TODO: print more lines for context.
                // i.e. print the entirety of the current line(s) as well as the line before and the line after
                out.println(text.substring(issue.getOffset(), issue.getOffset() + issue.getLength()));
            }
        }
    }

    private void outputJson(OutputStream outStream, List<Issue> issues, boolean errorOccurred) throws IOException {
        OutputStreamWriter streamWriter = new OutputStreamWriter(outStream, StandardCharsets.UTF_8);
        JSONWriter writer = new JSONWriter(streamWriter);
        writer.object();
        writer.key("issues").array();
        for (Issue issue : issues) {
            writer.object()
                .key("severity").value(issue.getSeverity().toString())
                .key("code").value(issue.getCode())
                .key("location").object()
                    .key("line").value(issue.getLineNumber())
                    .key("column").value(issue.getColumn())
                .endObject()
                .key("message").value(issue.getMessage())
            .endObject();
        }
        writer.endArray();
        writer.key("errorOccurred").value(errorOccurred);
        writer.endObject();
        streamWriter.close();
    }

    @Override
    public Integer call() throws IOException {
        InputStream fileStream = new FileInputStream(file);
        boolean errorOccurred = false;
        try {
            Injector injector = new HandProofStandaloneSetup().createInjectorAndDoEMFRegistration();
            ResourceSet rs = injector.getInstance(ResourceSet.class);
            Resource resource = rs.createResource(URI.createURI("foo.proof"));
            LoggingValidationMessageHandler msgHandler = (LoggingValidationMessageHandler) injector.getInstance(IValidationMessageHandler.class);
            msgHandler.setShouldHandleOutput(false);
            if(outputFormat == CheckerOutputFormat.plain) {
                System.out.println("Loading file...");
            }
            resource.load(fileStream, null);

            if(outputFormat == CheckerOutputFormat.plain) {
                System.out.println("Running validation... (this may take a while)");
            }

            IValidationFilePathProvider validationFilePathProvider = injector.getInstance(IValidationFilePathProvider.class);
            validationFilePathProvider.setPath(file.toPath().toAbsolutePath().getParent().toAbsolutePath().toString());
            IResourceValidator validator = injector.getInstance(IResourceValidator.class);
            List<Issue> issues;
            if(!fullCheck) {
                issues = validator.validate(resource,
                        CheckMode.NORMAL_AND_FAST, CancelIndicator.NullImpl);
            } else {
                issues = validator.validate(resource,
                        CheckMode.ALL, CancelIndicator.NullImpl);
            }
            errorOccurred = issues.stream().anyMatch(issue -> issue.getSeverity() == Severity.ERROR);
            
            switch(outputFormat) {
            case plain:
                this.outputPlain(System.out, file.toURI(), issues);
                break;
            case json:
                this.outputJson(System.out, issues, errorOccurred);
                break;
            }

            GeneratorDelegate generator = injector.getInstance(GeneratorDelegate.class);

            // For writing to real files using Java.IO.File
            //	        JavaIoFileSystemAccess fsa = new JavaIoFileSystemAccess();
            //	        Guice.createInjector(new AbstractGenericModule() {
            //				@SuppressWarnings("unused")
            //				public Class<? extends IEncodingProvider> bindIEncodingProvider() {
            //					return IEncodingProvider.Runtime.class;
            //				}
            //			}).injectMembers(fsa);
            //	        Path path = FileSystems.getDefault().getPath("").toAbsolutePath();
            //	        fsa.setOutputPath(path.toString());

            // For writing to emulated in-memory files
            InMemoryFileSystemAccess fsa = new InMemoryFileSystemAccess();

            if(generateOptions != null && generateOptions.generate) {
                generator.doGenerate(resource, fsa);
                CharSequence fileContents = fsa.getTextFiles().entrySet().iterator().next().getValue();
                File outfile;
                if(generateOptions.outfile == null) {
                    Path path = FileSystems.getDefault().getPath("").toAbsolutePath();
                    outfile = path.resolve("output.lisp").toFile();
                } else {
                    outfile = generateOptions.outfile;
                }
                FileWriter writer = new FileWriter(outfile, StandardCharsets.UTF_8);
                writer.append(fileContents);
                writer.close();
            }
        } finally {
            fileStream.close();
        }
        if(errorOccurred) {
            return 1;
        } else {
            return 0;
        }
    }
}
