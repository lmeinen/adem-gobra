Running the following commands from the base directory (directory where the readme resides) will verify the respective generated encoding using the provided Gobra jar.


java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i claim/claim.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i fact/fact.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i fresh/fresh.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i iospec/permissions_out.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i iospec/permissions_in.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i iospec/permissions_Verifier_internal.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i iospec/permissions_AuthorityVerifier_internal.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i iospec/permissions_in.gobra iospec/permissions_out.gobra iospec/permissions_Verifier_internal.gobra iospec/Verifier.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i iospec/permissions_in.gobra iospec/permissions_out.gobra iospec/permissions_AuthorityVerifier_internal.gobra iospec/AuthorityVerifier.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i place/place.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i pub/pub.gobra
java -Xss128m -jar /home/lasse/repos/gobra/target/scala-2.13/gobra.jar -I ./ --module github.com/adem-wg/adem-proto -i term/term.gobra