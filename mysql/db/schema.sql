/*!40101 SET @OLD_CHARACTER_SET_CLIENT=@@CHARACTER_SET_CLIENT */;
/*!40101 SET @OLD_CHARACTER_SET_RESULTS=@@CHARACTER_SET_RESULTS */;
/*!40101 SET @OLD_COLLATION_CONNECTION=@@COLLATION_CONNECTION */;
/*!50503 SET NAMES utf8mb4 */;
/*!40103 SET @OLD_TIME_ZONE=@@TIME_ZONE */;
/*!40103 SET TIME_ZONE='+00:00' */;
/*!40014 SET @OLD_UNIQUE_CHECKS=@@UNIQUE_CHECKS, UNIQUE_CHECKS=0 */;
/*!40014 SET @OLD_FOREIGN_KEY_CHECKS=@@FOREIGN_KEY_CHECKS, FOREIGN_KEY_CHECKS=0 */;
/*!40101 SET @OLD_SQL_MODE=@@SQL_MODE, SQL_MODE='NO_AUTO_VALUE_ON_ZERO' */;
/*!40111 SET @OLD_SQL_NOTES=@@SQL_NOTES, SQL_NOTES=0 */;

--
-- Table structure for table `arguments_on_entry`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `arguments_on_entry` (
  `node_id` int unsigned DEFAULT NULL,
  `name` char(255) NOT NULL DEFAULT '',
  `value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`name`),
  CONSTRAINT `arguments_on_entry_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `arguments_when_returning`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `arguments_when_returning` (
  `node_id` int unsigned DEFAULT NULL,
  `name` char(255) NOT NULL DEFAULT '',
  `value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`name`),
  CONSTRAINT `arguments_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`id`),
  CONSTRAINT `arguments_when_returning_fk_2` FOREIGN KEY (`node_id`, `name`) REFERENCES `arguments_on_entry` (`node_id`, `name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `global_variables_on_entry`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `global_variables_on_entry` (
  `node_id` int unsigned DEFAULT NULL,
  `name` char(255) NOT NULL DEFAULT '',
  `value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`name`),
  CONSTRAINT `global_variables_on_entry_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`id`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `global_variables_when_returning`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `global_variables_when_returning` (
  `node_id` int unsigned DEFAULT NULL,
  `name` char(255) NOT NULL DEFAULT '',
  `value` blob NOT NULL,
  UNIQUE KEY `node_id` (`node_id`,`name`),
  CONSTRAINT `global_variables_when_returning_fk_1` FOREIGN KEY (`node_id`) REFERENCES `nodes` (`id`),
  CONSTRAINT `global_variables_when_returning_fk_2` FOREIGN KEY (`node_id`, `name`) REFERENCES `global_variables_on_entry` (`node_id`, `name`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `nodes`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `nodes` (
  `id` int unsigned DEFAULT NULL,
  `parent_id` int unsigned DEFAULT NULL,
  `birth_order` int unsigned DEFAULT NULL,
  `function_name` blob NOT NULL,
  `return_value` blob NOT NULL,
  `object_on_entry` blob NOT NULL,
  `object_when_returning` blob NOT NULL,
  `creation_time` timestamp(6) NOT NULL DEFAULT CURRENT_TIMESTAMP(6),
  `finishing_time` timestamp(6) NULL DEFAULT NULL ON UPDATE CURRENT_TIMESTAMP(6),
  `finished` tinyint(1) NOT NULL DEFAULT '0',
  UNIQUE KEY `id` (`id`),
  UNIQUE KEY `parent_id` (`parent_id`,`birth_order`),
  CONSTRAINT `parent_node_exists` FOREIGN KEY (`parent_id`) REFERENCES `nodes` (`id`) ON DELETE CASCADE,
  CONSTRAINT `root_parent_id_zero_ow_lower_than_id` CHECK ((if((`id` = 0),(`parent_id` = 0),(`id` > `parent_id`)) = true))
) ENGINE=InnoDB DEFAULT CHARSET=latin1;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Table structure for table `schema_migrations`
--

/*!40101 SET @saved_cs_client     = @@character_set_client */;
/*!50503 SET character_set_client = utf8mb4 */;
CREATE TABLE `schema_migrations` (
  `version` varchar(255) COLLATE latin1_bin NOT NULL,
  PRIMARY KEY (`version`)
) ENGINE=InnoDB DEFAULT CHARSET=latin1 COLLATE=latin1_bin;
/*!40101 SET character_set_client = @saved_cs_client */;

--
-- Dumping routines for database 'ddc'
--
/*!40103 SET TIME_ZONE=@OLD_TIME_ZONE */;

/*!40101 SET SQL_MODE=@OLD_SQL_MODE */;
/*!40014 SET FOREIGN_KEY_CHECKS=@OLD_FOREIGN_KEY_CHECKS */;
/*!40014 SET UNIQUE_CHECKS=@OLD_UNIQUE_CHECKS */;
/*!40101 SET CHARACTER_SET_CLIENT=@OLD_CHARACTER_SET_CLIENT */;
/*!40101 SET CHARACTER_SET_RESULTS=@OLD_CHARACTER_SET_RESULTS */;
/*!40101 SET COLLATION_CONNECTION=@OLD_COLLATION_CONNECTION */;
/*!40111 SET SQL_NOTES=@OLD_SQL_NOTES */;

-- Dump completed

--
-- Dbmate schema migrations
--

LOCK TABLES `schema_migrations` WRITE;
INSERT INTO `schema_migrations` (version) VALUES
  ('20220522161939'),
  ('20220523165858'),
  ('20220523165910'),
  ('20220523165927'),
  ('20220523165938');
UNLOCK TABLES;
